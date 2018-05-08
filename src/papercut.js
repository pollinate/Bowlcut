import * as paperDefault from 'paper';

const paper = paperDefault.default;

paper.setup([2048, 2048]);

/*
  Papercut.JS - supplemental script for Bowlcut that uses Paper.js to
  calculate unions for characters within svg DOM elements

  Papercut expects to receive a DOM element with the following format:
  <g class="some-name">
    <path d="" fill="" stroke="" stroke-width="" stroke-linejoin="" stroke-linecap="">
    ...
  </g>
  This is the exact structure generated when using a Bowlcut instance's
  render function.
*/

/**
	 * papercut generates the union of each group of characters in an svg DOM element
	 * @param {Object} domElem - svg element generated from Bowlcut.
	 * @returns {Object} New svg DOM element with unions applied.
	 */
export default function papercut(domElem) {

  // parse the svg DOM element into separate path elements
  let pathArrays = [];
  domElem.childNodes.forEach(function getSeparatePaths(compoundPath) {

    if (compoundPath.tagName !== 'path') {
      return;
    }

    pathArrays.push([]);

    let charPaths = compoundPath.getAttribute('d') || '';
    let charFill = compoundPath.getAttribute('fill') || '';
    let charStroke = compoundPath.getAttribute('stroke') || '';
    let charStrokeWidth = compoundPath.getAttribute('stroke-width') || '';
    let charStrokeLinejoin = compoundPath.getAttribute('stroke-linejoin') || '';
    let charStrokeLinecap = compoundPath.getAttribute('stroke-linecap') || '';

    charPaths = charPaths.split('Z');

    charPaths.forEach(function stylePaths(path) {
      if (path.length > 0) {
        path = path.concat('Z');
        let tempPath = createSVGElement('path');
        tempPath.setAttribute('d', path);
        tempPath.setAttribute('fill', charFill);
        tempPath.setAttribute('stroke', charStroke);
        tempPath.setAttribute('stroke-width', charStrokeWidth);
        tempPath.setAttribute('stroke-linejoin', charStrokeLinejoin);
        tempPath.setAttribute('stroke-linecap', charStrokeLinecap);
        pathArrays[pathArrays.length - 1].push(tempPath);
      }
    });
  });

  // use paper.js to do the thing
  let wordGroups = [];
  pathArrays.forEach(function traverseWord(word) {
    let characters = [];
    // import each character into paper.js but keep track of them
    word.forEach(function putWordsToPaper(character, i) {
      characters[i] = paper.project.importSVG(character);
    });

    if (characters.length > 1) {
      // create a new array for union paths
      let newPaths = new Array(characters.length - 1);
      // unite the last two characters and keep track of it in the new array
      newPaths[newPaths.length - 1] = characters[characters.length - 2].unite(characters[characters.length - 1]);
      // do all of the unions and keep track of them in the new array
      for (let i = newPaths.length - 1; i > 0; i--) {
        newPaths[i - 1] = newPaths[i].unite(characters[i - 1]);
      }
      // characters is one element longer than the new array so remove
      // the last path from the paper project so it isn't exported
      characters[characters.length - 1].remove();
      // remove all paths from both arrays EXCEPT for the first
      for (let i = newPaths.length - 1; i > 0; i--) {
        newPaths[i].remove();
        characters[i].remove();
      }
      // we only care about the first element of the new array because it
      // has a path representing the union of all of the characters... so
      // kill the last remaining artifact: the first character
      characters[0].remove();
      // now that we only have one path left, the path representing all
      // unioned characters, export the contents of the project
    }

    wordGroups.push(paper.project.exportSVG({precision: 3}));
    // clear the project so subsequent uses of Papercut don't contain
    // paths from the previous union event
    paper.project.clear();
  });
  // create a container for the new paths and append them
  let wordGroup = createSVGElement('g');
  for (let i = 0; i < wordGroups.length; i++) {
    wordGroup.appendChild(wordGroups[i].firstChild);
  }

  return wordGroup;
}

function createSVGElement(elem) {
  return document.createElementNS('http://www.w3.org/2000/svg', elem);
}
