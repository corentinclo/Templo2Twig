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
const END_TEMPLO_REGEX = /::end::/;
const FOREACH_TEMPLO_REGEX = /(::foreach\s)(.*)(\s)(.*)(::)/g;
const RAW_TEMPLO_REGEX = /(::raw\s)(.*)(::)/g;
const RAW_CONTENT_TEMPLO_REGEX = /::raw\s__content__::/g
const FILL_TEMPLO_REGEX = /(::fill\s)(.*)(::)/g;
const SET_TEMPLO_REGEX = /(::set\s)(.*)(::)/g;
const USE_TEMPLO_REGEX = /(::use\s)(.*)(::)/;
const SWITCH_TEMPLO_REGEX = /::switch\s(.*)::/;
const CASE_TEMPLO_REGEX = /::case::\s+(.*)/;
const PRINT_TEMPLO_REGEX = /(::)(.*)(::)/g;
const MACRO_USAGE_TEMPLO_REGEX = /(\$\$)(\w+)(\(.*\))/g;
const MACRO_ATTR_TEMPLO_REGEX = /(<\w+\s)(\w+(=".*")*\s)*(\$\$)(\w+)(\(.*\))(.*>)/g
const COND_TEMPLO_REGEX = /(::cond\s)(.*)(::)/g;
const ATTR_CLASS_TEMPLO_REGEX = /::attr\sclass\sif\((.*)\)\s+(.*)(::>)/g;
const ATTR_CHECKED_TEMPLO_REGEX = /::attr\schecked\s\((.*)\)::/g;
const ATTR_SELECTED_TEMPLO_REGEX = /::attr\sselected\s\((.*)\)::/g;
const NOT_TEMPLO_REGEX = /(.*)(!)([^=].*)/g;
const AND_TEMPLO_REGEX = /(.*)(&&)(.*)/g;
const OR_TEMPLO_REGEX = /(.*)(\|\|)(.*)/g;
const MACRO_START_TAG_TEMPLO = /<macro name=\"(.+)\">/g;
const MACRO_END_TAG_TEMPLO = /<\/macro>/g;
const MACROS_START_TAG_TEMPLO = /<macros>/;
const MACROS_END_TAG_TEMPLO = /<\/macros>/;

// Statement constants
const statement = {
    IF: "if",
    FOR: "for",
    SET: "set",
    BLOCK: "block"
} 


// String templates
const TEMPLATE_MACRO = "TEMPLATE_MACRO_";
const TEMPLATE_COND = "TEMPLATE_COND_";
const TEMPLATE_USE = "TEMPLATE_USE";
const TEMPLATE_ATTR_CLASS = "TEMPLATE_ATTR_CLASS_";
const TEMPLATE_ATTR_CHECKED = "TEMPLATE_ATTR_CHECKED_";
const TEMPLATE_ATTR_SELECTED = "TEMPLATE_ATTR_SELECTED_";

// States
let previousStatement = [];
let macrosAreImported = false;
let switchCasePosition = 0;
let switchCaseCondition = "";
const templateMacroAttributes = [];
const templateCondAttributes = [];
let templateUseFileName = "";
const templateAttrClassAttributes = [];
const templateAttrCheckedAttributes = [];
const templateAttrSelectedAttributes = [];

/*
 * 
 * Convert a Templo node to Twig (and recursively converts its childNodes)
 *
 */

const convertToTwig = (node) => {
    if (!node) {
        return
    }

    if (node.attributes) {
        checkAttributes(node);
    }

    if (node.nodeName === '#text') {
        if (SWITCH_TEMPLO_REGEX.test(node.nodeValue)) {
            node.nodeValue = convertSwitch(node.nodeValue);
            previousStatement.push(statement.IF);
        }
        if (CASE_TEMPLO_REGEX.test(node.nodeValue)) {
            node.nodeValue = convertCase(node.nodeValue);
        }
        if (IF_TEMPLO_REGEX.test(node.nodeValue)) {
            convertIf(node);
            previousStatement.push(statement.IF);
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
        if (FOREACH_TEMPLO_REGEX.test(node.nodeValue)) {
            node.nodeValue = convertForeach(node.nodeValue);
            previousStatement.push(statement.FOR);
        }
        if (RAW_CONTENT_TEMPLO_REGEX.test(node.nodeValue)) {
            node.nodeValue = convertRawContent(node.nodeValue);
        }
        if (RAW_TEMPLO_REGEX.test(node.nodeValue)) {
            node.nodeValue = convertRaw(node.nodeValue);
        }
        if (FILL_TEMPLO_REGEX.test(node.nodeValue)) {
            node.nodeValue = convertFill(node.nodeValue);
            previousStatement.push(statement.SET);
        }
        if (SET_TEMPLO_REGEX.test(node.nodeValue)) {
            node.nodeValue = convertSet(node.nodeValue);
            previousStatement.push(statement.SET);
        }
        if (PRINT_TEMPLO_REGEX.test(node.nodeValue)) {
            node.nodeValue = convertPrint(node.nodeValue);
        }
        if (node.nodeValue.includes(TEMPLATE_MACRO)) {
            node.nodeValue = fillInTwigMacro(node.nodeValue);
        }
    } else if (node.childNodes) {
        const array = Array.from(node.childNodes);
        array.map(child => {
            // If a node contains several directives, we will seperates each directives into a separated node.
            const splittedNodes = splitNodeByStatements(child);
            if (!splittedNodes.length) {
                convertToTwig(child);
            } else {
                splittedNodes.forEach(splittedNode => {
                    convertToTwig(splittedNode);
                })
                // Reconcat node and return
                child.nodeValue = splittedNodes.reduce((concatenated, splittedNode) => `${concatenated}${splittedNode.nodeValue}`, '');
                child.data = child.nodeValue;
            }
        })
    }
    node.data = node.nodeValue;
}

const splitNodeByStatements = (node) => {
    if (!node.nodeValue) {
        return [];
    }
    const splittedNodes = [];
    let split = node.nodeValue.match(/.+?(?=::(foreach|if|set))(.*)/s);
    splittedNodes.push(node);
    split = split && split[2];
    while (split) {
        const splittedNode = doc.createTextNode(split);
        splittedNodes.push(splittedNode);
        split = split.match(/.+?(?=::(foreach|if|set))(.*)/s)
        split = split && split[2];
    }

    splittedNodes.forEach((node, i) => {
        if (i === splittedNodes.length - 1) {
            return;
        }
        node.nodeValue = node.nodeValue.replace(splittedNodes[i+1].nodeValue, '');
        node.data = node.nodeValue;
    })
    return splittedNodes;
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
            attribute.value = 'TEMPLATE_ATTRIBUTE';
        }
        else if (attribute.name === "class" && attribute.value.startsWith(TEMPLATE_ATTR_CLASS)) {
            const templateAttrPosition = attribute.value.substring(TEMPLATE_ATTR_CLASS.length);
            attribute.name = templateAttrClassAttributes[templateAttrPosition];
            attribute.value = 'TEMPLATE_ATTRIBUTE';
        }
        else if (attribute.name === "checked" && attribute.value.startsWith(TEMPLATE_ATTR_CHECKED)) {
            const templateAttrPosition = attribute.value.substring(TEMPLATE_ATTR_CHECKED.length);
            attribute.name = templateAttrCheckedAttributes[templateAttrPosition];
            attribute.value = 'TEMPLATE_ATTRIBUTE';
        }
        else if (attribute.name === "selected" && attribute.value.startsWith(TEMPLATE_ATTR_SELECTED)) {
            const templateAttrPosition = attribute.value.substring(TEMPLATE_ATTR_SELECTED.length);
            attribute.name = templateAttrSelectedAttributes[templateAttrPosition];
            attribute.value = 'TEMPLATE_ATTRIBUTE';
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

    const macroAttrConvertedTwig = "$1$2{{ macros.$5$6 }}$7";
    const macroUsageConvertedTwig = "<div macro> {{ macros.$2$3 }} </div>";
    fileAsString = fileAsString.replace(MACRO_ATTR_TEMPLO_REGEX, macroAttrConvertedTwig);
    fileAsString = fileAsString.replace(MACRO_USAGE_TEMPLO_REGEX, macroUsageConvertedTwig);

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

    /* ::cond */

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

    /* ::use */

    // Get and store the converted Twig cond attribute
    const useMatch = fileAsString.match(USE_TEMPLO_REGEX);
    if (useMatch) {
        templateUseFileName = useMatch && useMatch[2];
    
        // Replace the Twig use attribute by a template string in an HTML tag
        const useTemplateString = `<html ${TEMPLATE_USE}='${TEMPLATE_USE}'>`;
        fileAsString = fileAsString.replace(USE_TEMPLO_REGEX, useTemplateString);
        const lastEndTemploDirective = fileAsString.match(/::end::(?![\s\S]*::end::)/);
        fileAsString = fileAsString.replace(/::end::(?![\s\S]*::end::)/, '</html>')
    }
    
    /* ::attr class */
    fileAsString = preConvertAttrAttributes(fileAsString, "class");

    /* ::attr checked */
    fileAsString = preConvertAttrAttributes(fileAsString, "checked");

    /* ::attr selected */
    fileAsString = preConvertAttrAttributes(fileAsString, "selected");

    return fileAsString;
}

const preConvertAttrAttributes = (fileAsString, attr) => {
    let template;
    let attrConvertedTwig;
    let regex;
    let templateAttrAttributes;
    if (attr === "class") {
        regex = ATTR_CLASS_TEMPLO_REGEX;
        template = TEMPLATE_ATTR_CLASS;
        attrConvertedTwig = `class={{ $1 ? "$2" : "''"}}`;
        templateAttrAttributes = templateAttrClassAttributes;
    } else if (attr === "checked") {
        regex = ATTR_CHECKED_TEMPLO_REGEX;
        template = TEMPLATE_ATTR_CHECKED;
        attrConvertedTwig = `${attr}={{ $1 }}`;
        templateAttrAttributes = templateAttrCheckedAttributes;
    } else if (attr === "selected") {
        regex = ATTR_SELECTED_TEMPLO_REGEX;
        template = TEMPLATE_ATTR_SELECTED;
        attrConvertedTwig = `${attr}={{ $1 }}`;
        templateAttrAttributes = templateAttrSelectedAttributes;
    }
    fileAsString = fileAsString.replace(regex, attrConvertedTwig);

    const attrMatches = fileAsString.match(new RegExp(`${attr}={{.*}}`, 'g'));
    if (attrMatches) {
        attrMatches.forEach(m => {
            templateAttrAttributes.push(m);
        })
        templateAttrAttributes && templateAttrAttributes.forEach((_, i) => {
            fileAsString = fileAsString.replace(new RegExp(`${attr}={{.*}}`), `${attr}="${template}${i}"`);
        })
    }
    
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
    let converted = value;
    let endTwig = "";
    while(converted.match(END_TEMPLO_REGEX)) {
        let endTwig = `{% end${previousStatement.pop()} %}`;
        converted = converted.replace(END_TEMPLO_REGEX, endTwig);
    }
    return converted;
}

const convertForeach = (value) => {
    const replacedTwigRegex = "{% for $2 in $4 %}";
    return value.replace(FOREACH_TEMPLO_REGEX, replacedTwigRegex);
}

const convertRawContent = (value) => {
    const replacedTwigRegex = "{% block $2 %}{% endblock %}";
    return value.replace(RAW_CONTENT_TEMPLO_REGEX, replacedTwigRegex);
}

const convertRaw = (value) => {
    const replacedTwigRegex = "{{ $2|raw }}";
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

const convertSwitch = (value) => {
    switchCaseCondition = value.match(SWITCH_TEMPLO_REGEX)[1];
    switchCasePosition = 0;
    while (value.match(CASE_TEMPLO_REGEX)) {
        value = convertCase(value);
    }
    return value.replace(SWITCH_TEMPLO_REGEX, "");
}

const convertCase = (value) => {
    const statement = !switchCasePosition ? 'if' : 'elseif';
    const replacedTwigRegex = `{% ${statement} ${switchCaseCondition}.index == ${switchCasePosition} %}\n$1`;
    value = value.replace(CASE_TEMPLO_REGEX, replacedTwigRegex);
    switchCasePosition += 1;
    return value;
}

const convertPrint = (value) => {
    const replacedTwigRegex = "{{$2}}";
    return value.replace(PRINT_TEMPLO_REGEX, replacedTwigRegex);
}

/*
 * 
 * Extends
 *
 */

const fillInUseTemplate = (fileAsString) => {
    if (!templateUseFileName) {
        return fileAsString
    }
    const twigFileName = templateUseFileName.replace(".mtt", ".twig");
    const replacedTwigExtends = `{% extends ${twigFileName} %}\n{% block content %}`
    fileAsString = fileAsString.replace(`<html ${TEMPLATE_USE}="${TEMPLATE_USE}" xmlns="http://www.w3.org/1999/xhtml">`, replacedTwigExtends); 
    fileAsString = fileAsString.replace('</html>', '{% endblock %}')
    return fileAsString
}

/*
 * 
 * MACROS
 *
 */

const importMacros = (node) => {
    const importMacrosNode = doc.createTextNode("\n{% import 'macros.html' as macros %}")
    const body = node.ownerDocument.getElementsByTagName("body")[0];
    if (!body) {
        const firstChild = node.ownerDocument.firstChild;
        firstChild.insertBefore(importMacrosNode, firstChild.firstChild);
    } else {
        body.insertBefore(importMacrosNode, body.firstChild);
    }
    
    macrosAreImported = true;
}

const fillInTwigMacro = (value) => {
    const firstSubstring = value.substring(value.indexOf(TEMPLATE_MACRO) + TEMPLATE_MACRO.length);
    const position = firstSubstring.substring(0, firstSubstring.indexOf('='));
    return value.replace(`${TEMPLATE_MACRO}${position}='${TEMPLATE_MACRO}${position}'`, templateMacroAttributes[position]); 
}

const removeTwigMacroAttributeValues = (string) => {
    const stringToBeRemoved ='="TEMPLATE_ATTRIBUTE"';
    while (string.match(stringToBeRemoved)) {
        string = string.replace(stringToBeRemoved, '');
    }
    return string;
}

const removeDivAroundMacroUsage = (string) => {
    const divAroundMacroUsageRegex = /<div\smacro="macro">\s({{\smacros.insert(.*)\s}})\s<\/div>/g;
    return string.replace(divAroundMacroUsageRegex, '$1');
}

const convertMacroDefinitions = (fileAsString) => {
    fileAsString = fileAsString.replace(MACRO_START_TAG_TEMPLO, "{% macro $1 %}")
    fileAsString = fileAsString.replace(MACRO_END_TAG_TEMPLO, "{% endmacro %}")
    fileAsString = fileAsString.replace(MACROS_START_TAG_TEMPLO, "")
    fileAsString = fileAsString.replace(MACROS_END_TAG_TEMPLO, "")
    fileAsString = convertPrint(fileAsString)

    return fileAsString;
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

    if (fileAsString.startsWith("<macros>")) {
        fileAsString = convertMacroDefinitions(fileAsString);

    } else {
        // Because the DOM parser won't recognize Templo attributes such as macros and ::cond, it will ignore them during the parsing.
        // That's why we need to convert them into a template string before to start the DOM parsing. Then the DOM parsing will properly
        // Recognize the template string which we'll be able to convert to Twig.
        fileAsString = preConvertAttributes(fileAsString);

        doc = parser.parseFromString(fileAsString, "text/html");

        doc.childNodes = Array.from(doc.childNodes).map(convertToTwig);
    }

    // Convert Document back to string
    const serializer = new XMLSerializer();
    fileAsString = serializer.serializeToString(doc);

    // Remove Twig macro attributes
    fileAsString = removeTwigMacroAttributeValues(fileAsString);

    // Remove div around macro usage that we added earlier 
    fileAsString = removeDivAroundMacroUsage(fileAsString);

    // Fill in use/extends template string
    fileAsString = fillInUseTemplate(fileAsString);

    // Remove remaining double colon
    fileAsString = removeTemploDoubleColon(fileAsString);

    // The DOM parser will add the xml namespace to the document but we don't want it.
    fileAsString = fileAsString.replace(' xmlns="http://www.w3.org/1999/xhtml"', '');
}

// JS
// const client = new XMLHttpRequest();
// client.open('GET', '/file.templo');
// client.onreadystatechange = function(e) {
//  if (e.currentTarget.readyState !== 4) {
//      return
//  }
//   fileAsString = client.responseText;

//   main()
// }
// client.send();

function getArgs () {
    const args = {};
    process.argv
        .slice(2, process.argv.length)
        .forEach( arg => {
        // long arg
        if (arg.slice(0,2) === '--') {
            const longArg = arg.split('=');
            const longArgFlag = longArg[0].slice(2,longArg[0].length);
            const longArgValue = longArg.length > 1 ? longArg[1] : true;
            args[longArgFlag] = longArgValue;
        }
        // flags
        else if (arg[0] === '-') {
            const flags = arg.slice(1,arg.length).split('');
            flags.forEach(flag => {
            args[flag] = true;
            });
        }
    });
    return args;
}
const args = getArgs();

const inputDirectory = args["input"];
const outputDirectory = args["output"];

const inputDirectoryPath = path.join(__dirname, inputDirectory);
const outputDirectoryPath = path.join(__dirname, outputDirectory);

console.log(`Will scan ${inputDirectoryPath} for Templo files.`)

fs.readdir(inputDirectoryPath, function (err, files) {
    if (err) {
        return console.log('Unable to scan directory: ' + err);
    } 
    files.forEach(function (fileName) {
        // Do whatever you want to do with the file
        const indexOfTemploExtension = fileName.indexOf(".mtt");
        if (indexOfTemploExtension === -1) {
            return;
        }
        console.log('\n ------ \nFound Templo file: ', fileName);
        fileAsString = bufferFile(fileName);
        function bufferFile(relPath) {
            return fs.readFileSync(path.join(__dirname, relPath), { encoding: 'utf8' });
        }

        console.log('Converting Templo file...');
        main();

        const twigFileName = fileName.replace(".mtt", ".twig");
        const outputFilePath = `${outputDirectoryPath}/${twigFileName}`;
        // We make sure output directory exists
        fs.mkdirSync(outputDirectoryPath, { recursive: true })
        fs.writeFile(outputFilePath, fileAsString, (err) => {
              if (err) throw err;
              console.log('\nThe converted Twig file has been saved to', outputFilePath);
            });
        });
});
