const DOMParser = require('xmldom').DOMParser;
const XMLSerializer = require('xmldom').XMLSerializer;
const fs = require('fs');
const path = require('path');

/*
 * 
 * Constants
 *
 */

const IF_TEMPLO_REGEX = /(::if\s)(.*)(::)/g;
const ELSEIF_TEMPLO_REGEX = /(::elseif\s)(.*)(::)/g;
const ELSE_TEMPLO_REGEX = /::else::/g;
const END_TEMPLO_REGEX = /::end::/g;
const FOREACH_TEMPLO_REGEX = /(::foreach\s)(.*)(\s)(.*)(::)/g;
const RAW_TEMPLO_REGEX = /(::raw\s)(.*)(::)/g;
const FILL_TEMPLO_REGEX = /(::fill\s)(.*)(::)/g;
const SET_TEMPLO_REGEX = /(::set\s)(.*)(::)/g;
const USE_TEMPLO_REGEX = /(::use\s)(.*)(::)/g;
const PRINT_TEMPLO_REGEX = /(::)(.*)(::)/g;
const MACRO_TEMPLO_REGEX = /(\$\$)(\w+)(\(.*\))/g;
const COND_TEMPLO_REGEX = /(::cond\s)(.*)(::)/g;
const NOT_TEMPLO_REGEX = /(.*)(!)(.*)/g;
const AND_TEMPLO_REGEX = /(.*)(&&)(.*)/g;
const OR_TEMPLO_REGEX = /(.*)(\|\|)(.*)/g;

// Statement constants
const IF = "if";
const FOR = "for";
const SET = "set";
const BLOCK = "block";

// Macros definitions
const MACROS_NODE_NAME = "macros";
const MACRO_NODE_NAME = "macro";

const TEMPLATE_MACRO = "TEMPLATE_MACRO_";
const TEMPLATE_COND = "TEMPLATE_COND_";

// States
let currentStatement = undefined;
let currentFileIsDocument = false;
let macrosAreImported = false;
const templateMacroAttributes = [];
const templateCondAttributes = [];

/*
 * 
 * Convert a Templo node to Twig (and recursively converts its childNodes)
 *
 */

const convertToTwig = (node) => {
	if (!node) {
		return
	}

	if (node.nodeName.toLowerCase() === MACROS_NODE_NAME) {
		convertMacrosDefinitions(node)
		return node;
	}

	if (node.attributes) {
		checkAttributes(node);
	}

	if (node.nodeName === '#text') {
		if (IF_TEMPLO_REGEX.test(node.nodeValue)) {
			convertIf(node);
			currentStatement = IF;
		}
		else if (ELSEIF_TEMPLO_REGEX.test(node.nodeValue)) {
			node.nodeValue = convertElseIf(node.nodeValue);
		}
		else if (ELSE_TEMPLO_REGEX.test(node.nodeValue)) {
			node.nodeValue = convertElse(node.nodeValue);
		}
		else if (END_TEMPLO_REGEX.test(node.nodeValue)) {
			node.nodeValue = convertEnd(node.nodeValue);
		}
		else if (FOREACH_TEMPLO_REGEX.test(node.nodeValue)) {
			node.nodeValue = convertForeach(node.nodeValue);
			currentStatement = FOR;
		}
		else if (RAW_TEMPLO_REGEX.test(node.nodeValue)) {
			node.nodeValue = convertRaw(node.nodeValue);
		}
		else if (FILL_TEMPLO_REGEX.test(node.nodeValue)) {
			node.nodeValue = convertFill(node.nodeValue);
			currentStatement = SET;
		}
		else if (SET_TEMPLO_REGEX.test(node.nodeValue)) {
			node.nodeValue = convertSet(node.nodeValue);
			currentStatement = SET;
		}
		else if (USE_TEMPLO_REGEX.test(node.nodeValue)) {
			convertUse(node);
			currentStatement = BLOCK;
		}
		else if (PRINT_TEMPLO_REGEX.test(node.nodeValue)) {
			node.nodeValue = convertPrint(node.nodeValue);
		}
		else if (node.nodeValue.includes(TEMPLATE_MACRO)) {
			node.nodeValue = fillInTwigMacro(node.nodeValue);
		}
	} else if (node.childNodes) {
		const array = Array.from(node.childNodes);
		array.map(child => {
			convertToTwig(child)
		})
	}
	node.data = node.nodeValue;
}

/*
 * 
 * Convert attributes
 *
 */

const checkAttributes = (node) => {
	for (let i = 0 ; i < node.attributes.length ; i++) {
		const attribute = node.attributes[i];
		if (attribute.name.startsWith(TEMPLATE_COND)) {
			const templateCondAttributePosition = attribute.name.substring(TEMPLATE_COND.length);
			const condition = templateCondAttributes[templateCondAttributePosition];
			convertCondAttribute(node, attribute, condition);
		}
		else if (attribute.name.startsWith(TEMPLATE_MACRO)) {
			if (!macrosAreImported) {
				importMacros(node);
			}
			const templateMacroAttributePosition = attribute.name.substring(TEMPLATE_MACRO.length);
			attribute.name = templateMacroAttributes[templateMacroAttributePosition];
			attribute.value = 'TEMPLATE_MACRO_ATTRIBUTE';
		}
		else if (PRINT_TEMPLO_REGEX.test(attribute.value)) {
			attribute.value = convertPrint(attribute.value);
		}
	}
}

const convertCondAttribute = (node, condAttribute, condition) => {
	const twigIfNode = doc.createTextNode(`{% if ${condition.substring(3).slice(0,-3)} %}\n`);
	const twigEndIfNode = doc.createTextNode("\n{% endif %}");
	node.parentNode.insertBefore(twigIfNode, node);
	node.parentNode.insertBefore(twigEndIfNode, node.nextSibling);

	node.removeAttribute(condAttribute.name);
	node.removeAttribute(condition.name);
}

// This method will replace Templo attributes by a template string that the DOM parser will be able to parse.
// Later, these template strings will be replaced by the correct converted Twig attribute.
const preConvertAttributes = (fileAsString) => {
	/* MACRO */

	const macroConvertedTwig = "{{ macros.$2$3 }}";
	fileAsString = fileAsString.replace(MACRO_TEMPLO_REGEX, macroConvertedTwig);

	// Get and store the converted Twig macro attribute
	const matches = fileAsString.match(/(<.*){{.*}}(.*>)/g);
		
	matches && matches.forEach(m => {
		const converted = m.replace(/<.*({{.*}}).*>/, "$1");
		templateMacroAttributes.push(removeTemploDoubleColon(converted));
	})
	// Replace the Twig macro attribute by a template string
	templateMacroAttributes.forEach((_, i) => {
		fileAsString = fileAsString.replace(/(<.*){{.*}}(.*>)/, `$1${TEMPLATE_MACRO}${i}='${TEMPLATE_MACRO}${i}'$2`);
	})

	// Finally, convert Templo macro's parameters
	const macroParameters = fileAsString.match(/{{\smacros\..*\s}}/g);
	macroParameters && macroParameters.forEach(p => {
		fileAsString = fileAsString.replace(p, removeTemploDoubleColon(p));
	});

	/* :cond */

	const condAttributeConvertedTwig = "{{ $2 }}";
	fileAsString = fileAsString.replace(COND_TEMPLO_REGEX, condAttributeConvertedTwig);

	// Get and store the converted Twig cond attribute
	const condMatches = fileAsString.match(/(<.*){{.*}}(.*>)/g);
	condMatches && condMatches.forEach(m => {
		const converted = m.replace(/<.*({{.*}}).*>/, "$1");
		templateCondAttributes.push(removeTemploDoubleColon(converted));
	})
	// Replace the Twig cond attribute by a template string
	templateCondAttributes && templateCondAttributes.forEach((_, i) => {
		fileAsString = fileAsString.replace(/(<.*){{.*}}(.*>)/, `$1${TEMPLATE_COND}${i}='${TEMPLATE_COND}${i}'$2`);
	})

	return fileAsString;
}

const removeTemploDoubleColon = (value) => {
	return value.replace(/::/g, '');
}

/*
 * 
 * Convert directives : ::if, ::foreach, ::raw, etc
 *
 */

const convertIf = (node) => {
	const replacedIfTwigRegex = "{% if $2 %}";
	node.nodeValue = node.nodeValue.replace(IF_TEMPLO_REGEX, replacedIfTwigRegex);

	// Check for conditional logic
	if (NOT_TEMPLO_REGEX.test(node.nodeValue)) {
		const replacedNotTwigRegex = "$1not $3";
		node.nodeValue = node.nodeValue.replace(NOT_TEMPLO_REGEX, replacedNotTwigRegex);
	}

	if (AND_TEMPLO_REGEX.test(node.nodeValue)) {
		const replacedAndTwigRegex = "$1and$3";
		node.nodeValue = node.nodeValue.replace(AND_TEMPLO_REGEX, replacedAndTwigRegex);
	}

	if (OR_TEMPLO_REGEX.test(node.nodeValue)) {
		const replacedOrTwigRegex = "$1or$3";
		node.nodeValue = node.nodeValue.replace(OR_TEMPLO_REGEX, replacedOrTwigRegex);
	}
}

const convertElseIf = (value) => {
	const replacedTwigRegex = "{% elseif $2 %}";
	return value.replace(ELSEIF_TEMPLO_REGEX, replacedTwigRegex);
}

const convertElse = (value) => {
	const elseTwig = "{% else %}";
	return value.replace(ELSE_TEMPLO_REGEX, elseTwig);
}

const convertEnd = (value) => {
	const endTwig = `{% end${currentStatement} %}`;
	currentStatement = undefined;
	return value.replace(END_TEMPLO_REGEX, endTwig);
}

const convertForeach = (value) => {
	const replacedTwigRegex = "{% for $2 in $4 %}";
	return value.replace(FOREACH_TEMPLO_REGEX, replacedTwigRegex);
}

const convertRaw = (value) => {
	const replacedTwigRegex = "{% block $2 %}{% endblock %}";
	return value.replace(RAW_TEMPLO_REGEX, replacedTwigRegex);
}

const convertFill = (value) => {
	const replacedTwigRegex = "{% set $2 %}";
	return value.replace(FILL_TEMPLO_REGEX, replacedTwigRegex);
}

const convertSet = (value) => {
	const replacedTwigRegex = "{% set $2 %}";
	return value.replace(SET_TEMPLO_REGEX, replacedTwigRegex);
}

const convertUse = (node) => {
	const replacedTwigRegex = "{% extends $2 %}";
	node.nodeValue = node.nodeValue.replace(USE_TEMPLO_REGEX, replacedTwigRegex);

	// Change file extension
	node.nodeValue = node.nodeValue.replace(".mtt", ".twig");

	const twigBlockNode = doc.createTextNode("{% block content %}\n");
	node.parentNode.insertBefore(twigBlockNode, node.nextSibling);
}

const convertPrint = (value) => {
	const replacedTwigRegex = "{{$2}}";
	return value.replace(PRINT_TEMPLO_REGEX, replacedTwigRegex);
}

/*
 * 
 * MACROS
 *
 */

const importMacros = (node) => {
	const importMacrosNode = doc.createTextNode("\n{% import 'macros.html' as macros %}")
	const body = node.ownerDocument.getElementsByTagName("body")[0];
	body.insertBefore(importMacrosNode, body.firstChild);
	macrosAreImported = true;
}

const convertMacro = (value) => {
	let converted = "{{ macros.$2(";
	// Convert macro's parameters
	const parameters = value.match(/::\w+::/g);
	if (parameters) {
		for (let i = 0 ; i < parameters.length ; i++) {
			converted += convertPrint(parameters[i]);
			if (i !== parameters.length - 1) {
				converted += ", "
			}
		}
	}
	converted += ") }}";
	return value.replace(MACRO_TEMPLO_REGEX, converted);
}

const convertMacrosDefinitions = (node) => {
	//while (node.childNodes.length) {
		node.childNodes = Array.from(node.childNodes).map(childNode => {
			if (childNode.nodeName === MACRO_NODE_NAME) {
				childNode = convertMacroDefinitions(childNode);
			}
			return childNode
		})
		// let childNode = node.firstChild;
		// if (childNode.nodeName === MACRO_NODE_NAME) {
		// 	childNode = convertMacroDefinitions(childNode);
		// }
		// if (childNode) {
		// 			node.parentNode.appendChild(childNode);

		// 		}else {
			// console.log("childNode", childNode)
		// 		}
	//}
	//node.remove();
}

const convertMacroDefinitions = (node) => {
	const attributes = node.attributes;
	const nameAttribute = attributes.getNamedItem("name");
	const macroName = nameAttribute && nameAttribute.value;
	const twigMacroNode = doc.createTextNode(`{% macro ${macroName} %}`);
	let lastMacroChildNode = undefined;
	const nodeSibling =  node.nextSibling;
	while (node.childNodes.length) { 
		lastMacroChildNode = node.firstChild;
		convertToTwig(lastMacroChildNode);
		node.parentNode.insertBefore(lastMacroChildNode, nodeSibling);
	}
	const twigEndMacroNode = doc.createTextNode('{% endmacro %}');
	lastMacroChildNode && node.parentNode.insertBefore(twigEndMacroNode, lastMacroChildNode.nextSibling);
	node.remove && node.remove();
	return twigMacroNode;
}

const fillInTwigMacro = (value) => {
	const firstSubstring = value.substring(value.indexOf(TEMPLATE_MACRO) + TEMPLATE_MACRO.length);
	const position = firstSubstring.substring(0, firstSubstring.indexOf('='));
	return value.replace(`${TEMPLATE_MACRO}${position}='${TEMPLATE_MACRO}${position}'`, templateMacroAttributes[position]); 
}

const removeTwigMacroAttributeValues = (string) => {
	const stringToBeRemoved ='="TEMPLATE_MACRO_ATTRIBUTE"';
	return string.replace(stringToBeRemoved, '');
}

/*
 * 
 * MAIN
 *
 */
const parser = new DOMParser();
let fileAsString;
let doc;

const main = () => {

	// Because the DOM parser won't recognize Templo attributes such as macros and ::cond, it will ignore them during the parsing.
	// That's why we need to convert them into a template string before to start the DOM parsing. Then the DOM parsing will properly
	// Recognize the template string which we'll be able to convert to Twig.
	fileAsString = preConvertAttributes(fileAsString);

	doc = parser.parseFromString(fileAsString, "text/html");

	if (fileAsString.startsWith("<html")) {
		currentFileIsDocument = true;
	}

	doc.childNodes = Array.from(doc.childNodes).map(convertToTwig);

	// Convert Document back to string
	const serializer = new XMLSerializer();
	let string = serializer.serializeToString(doc);
	if (currentFileIsDocument) {
		// Remove Twig macro attributes
		fileAsString = removeTwigMacroAttributeValues(string);	
	} else {
		fileAsString = fileAsString.replace('xmlns="http://www.w3.org/1999/xhtml"', '');
	}

	console.log(fileAsString);
}

fileAsString = bufferFile('/file.templo');
function bufferFile(relPath) {
    return fs.readFileSync(path.join(__dirname, relPath), { encoding: 'utf8' });
}

main();

fs.writeFile('./twig/file.twig', fileAsString, (err) => {
  if (err) throw err;
  console.log('The file has been saved!');
});

