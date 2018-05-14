import {Bowlcut} from '../dist/bundle.js';

const section1 = document.querySelector('#section1');
const slider = document.querySelector('#radius-slider');
var wordmark = new Bowlcut({
  text: ['BOWLCUT.JS'],
  colors: ['#90909f', '#f44280'],
  debug: false
});

const region = wordmark.addRegion({
  bounds: {
    x: 150,
    y: 150,
    width: 300,
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

var wmkGroup;



wordmark.loadFonts([['Modak-Regular', 'fonts/Modak-Regular.ttf']])
  .then(() => {

    // render a radial arch
    region.makeRadialArch(Number(slider.value));
    wmkGroup = wordmark.render(false);
    section1.appendChild(wmkGroup);

    // start listening to the slider
    slider.oninput = updateArch;
  });

function updateArch() {
  section1.removeChild(wmkGroup);
  region.makeRadialArch(Number(slider.value));
  wmkGroup = wordmark.render(false);
  section1.appendChild(wmkGroup);
}
