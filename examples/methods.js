import {Bowlcut} from '../dist/bundle.js';

const section1 = document.querySelector('#section1');
const section2 = document.querySelector('#section2');
const section3 = document.querySelector('#section3');
const section4 = document.querySelector('#section4');
const section5 = document.querySelector('#section5');
const customt = document.querySelector('#custom-t');
const customb = document.querySelector('#custom-b');


var wordmark = new Bowlcut({
  text: ['BOWLCUT.JS', 'A library for hairy SVG text manipulation'],
  colors: ['#cc9955', '#443355'],
  debug: false
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

    // render text that is split between regions
    wordmark.removeRegion(region);
    const dropcap = wordmark.addRegion({
      bounds: {
        x: 50,
        y: 50,
        width: 150,
        height: 250
      },
      font: 0,
      fill: 1,
      stroke: 0,
      slice: {
        0: [0,1]
      },
      stretchToWidth: true
    });
    dropcap.makeStraightPaths();

    const restofword = wordmark.addRegion({
      bounds: {
        x: 200,
        y: 50,
        width: 350,
        height: 200
      },
      font: 0,
      fill: 1,
      stroke: null,
      slice: {
        0: [1]
      },
      stretchToWidth: true
    });
    restofword.makeStraightPaths();

    const subtitle = wordmark.addRegion({
      bounds: {
        x: 200,
        y: 250,
        width: 350,
        height: 50
      },
      font: 0,
      fill: 1,
      stroke: 0,
      slice: {
        1: []
      },
      stretchToWidth: false
    });
    subtitle.makeStraightPaths();
    section5.appendChild(wordmark.render(true));
  });
