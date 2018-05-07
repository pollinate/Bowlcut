import {Bowlcut} from '../dist/bundle.js';

var target = document.querySelector('#target');
var wordmark = new Bowlcut({
  text: ['example', 'wordmark'],
  colors: ['#ff0000', '#00ccff']
});

//some example region data
var dataA = {
  bounds: {
    x: 128,
    y: 128,
    width: 256,
    height: 64
  },
  font: 1,
  fill: 0,
  stroke: 1,
  slice: {
    0: []
  },
  topPath: null,
  bottomPath: null,
  stretchToWidth: false,
  advanceWidthScale: 1.0
};

var dataB = {
  bounds: {
    x: 128,
    y: 224,
    width: 256,
    height: 64
  },
  font: 0,
  fill: 1,
  stroke: null,
  slice: {
    1: [4]
  },
  topPath: null,
  bottomPath: null
};

var regionA = wordmark.addRegion(dataA);
var regionB = wordmark.addRegion(dataB);

regionA.makeRadialArch(0.5);
regionB.makeArch(0, 0.3);

wordmark.loadFonts([
  ['Modak-Regular', 'fonts/Modak-Regular.ttf'],
  ['PassionOne-Bold', 'fonts/PassionOne-Bold.ttf']
])
  .then(() => {
    target.appendChild(wordmark.render());
  });
