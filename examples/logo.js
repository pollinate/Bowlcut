import {Bowlcut} from '../dist/bundle.js';

const target = document.querySelector('#target');
const hairTop = document.querySelector('#hair-top');
const hairBottom = document.querySelector('#hair-bottom');
const finalString = 'BOWLCUT.JS IS A LIBRARY FOR HAIRY SVG TEXT MANIPULATION BOWLCUT.JS';
const wordmark = new Bowlcut({
  text: [''],
  colors: ['#333333'],
  precision: 1
});
var wmkGroup;

//some example region data
var dataA = {
  bounds: {
    x: 0,
    y: 0,
    width: 326,
    height: 242
  },
  font: 0,
  fill: 0,
  stroke: null,
  slice: {
    0: []
  },
  topPath: hairTop,
  bottomPath: hairBottom,
  stretchToWidth: false,
  advanceWidthScale: 1.0
};

wordmark.addRegion(dataA);

wordmark.loadFonts([
  ['PassionOne-Bold', 'fonts/PassionOne-Bold.ttf']
])
  .then(() => {
    wordmark.text[0] = finalString.substr(0, 10);
    target.removeChild(hairTop);
    target.removeChild(hairBottom);
    wmkGroup = wordmark.render();
    target.appendChild(wmkGroup);
    return new Promise((res) => {
      setTimeout(res, 1000);
    });
  })
  .then(() => {
    let ic = 0;
    let iv = setInterval(() => {
      target.removeChild(wmkGroup);
      wordmark.text[0] = finalString.substr(ic, 10);
      wmkGroup = wordmark.render();
      target.appendChild(wmkGroup);
      ic++;
      if (ic > finalString.length - 10) {
        clearInterval(iv);
      }
    }, 120);
  });
