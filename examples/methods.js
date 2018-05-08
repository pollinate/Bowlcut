import {Bowlcut} from '../dist/bundle.js';

const section1 = document.querySelector('#section1');
const section2 = document.querySelector('#section2');
const section3 = document.querySelector('#section3');
const section4 = document.querySelector('#section4');
const customt = document.querySelector('#custom-t');
const customb = document.querySelector('#custom-b');


var wordmark = new Bowlcut({
  text: ['BOWLCUT.JS'],
  colors: ['#cc9955', '#443355']
});

const region = wordmark.addRegion({
  bounds: {
    x: 100,
    y: 150,
    width: 400,
    height: 100
  },
  font: 0,
  fill: 0,
  stroke: 1,
  slice: {
    0: []
  },
  topPath: null,
  bottomPath: null,
  stretchToWidth: true,
  advanceWidthScale: 1.0
});

wordmark.loadFonts([['Molle-Regular', 'fonts/Molle-Regular.ttf']])
  .then(() => {

    // plain render to the bounds
    region.makeStraightPaths();
    section1.appendChild(wordmark.render(true));

    // render a quadratic arch
    region.makeArch(0.75, 0.75);
    section2.appendChild(wordmark.render(true));

    // render a radial arch
    region.makeRadialArch(0.75);
    section3.appendChild(wordmark.render(true));

    // render between custom paths
    region.topPath = customt;
    region.bottomPath = customb;
    section4.appendChild(wordmark.render(true));
  });
