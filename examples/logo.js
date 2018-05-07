import {Bowlcut} from '../dist/bundle.js';

var target = document.querySelector('#target');
var finalString = 'BOWLCUT.JS IS A LIBRARY FOR HAIRY SVG TEXT MANIPULATION BOWLCUT.JS';
var wordmark = new Bowlcut({
  text: [''],
  colors: ['#333333']
});

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
  topPath: document.querySelector('#hair-top'),
  bottomPath: document.querySelector('#hair-bottom'),
  stretchToWidth: false,
  advanceWidthScale: 1.0
};

wordmark.addRegion(dataA);

wordmark.loadFonts([
  ['PassionOne-Bold', 'fonts/PassionOne-Bold.ttf']
])
  .then(() => {
    wordmark.text[0] = finalString.substr(0, 10);
    emptySVG(target);
    target.appendChild(wordmark.render());
    return new Promise((res) => {
      setTimeout(res, 1000);
    });
  })
  .then(() => {
    let ic = 0;
    let iv = setInterval(() => {
      emptySVG(target);
      wordmark.text[0] = finalString.substr(ic, 10);
      target.appendChild(wordmark.render());
      ic++;
      if (ic > finalString.length - 10) {
        clearInterval(iv);
      }
    }, 120);
  });

function emptySVG(svg) {
  let svgChildren = Array.from(svg.children);
  for (let child of svgChildren) {
    svg.removeChild(child);
  }
}
