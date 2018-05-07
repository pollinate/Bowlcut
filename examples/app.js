import {Bowlcut} from '../dist/bundle.js';

var staging = document.querySelector('#staging');

var mlgSelect = document.querySelector('#mlg-select');
var fontSelect = document.querySelector('#font-select');

var textline1 = document.querySelector('#textline1');
var textline2 = document.querySelector('#textline2');
var textline3 = document.querySelector('#textline3');

var color1 = document.querySelector('#color1');
var color2 = document.querySelector('#color2');
var color3 = document.querySelector('#color3');

var templates = [];
var fontnames = [
  'Modak-Regular',
  'PassionOne-Bold'
];
var activeTemplateIndex = 6;
var activeFont = fontnames[0];

var text = [
  textline1.value,
  textline2.value,
  textline3.value
];

var colors = [
  color1.value,
  color2.value,
  color3.value
];

Promise.all([loadTemplates()])
  .then(() => {

    fontnames.map((fn) => {
      let option = document.createElement('option');
      option.value = fn;
      option.textContent = fn;
      if (fn === activeFont) {
        option.selected = true;
      }
      fontSelect.appendChild(option);
      fontSelect.value = fn;
    });

    mlgSelect.onchange = function handleMLGSelect() {
      activeTemplateIndex = mlgSelect.value;
      drawText();
    };

    fontSelect.onchange = function handleFontSelect() {
      activeFont = fontSelect.value;
      drawText();
    };

    textline1.oninput = textline2.oninput = textline3.oninput = function handleTextInput() {
      text[0] = textline1.value;
      text[1] = textline2.value;
      text[2] = textline3.value;
      drawText();
    };

    color1.oninput = color2.oninput = color3.oninput = function handleColorInput() {
      colors[0] = color1.value;
      colors[1] = color2.value;
      colors[2] = color3.value;
      drawText();
    };

    drawText();
  });

function drawText() {

  var mlg = new Bowlcut({ text, colors, debug: true });
  mlg.loadFonts([[activeFont, `fonts/${activeFont}.ttf`]])
    .then(() => {
      emptySVG(staging);

      templates[activeTemplateIndex].regions.forEach(function renderRegion(rg) {

        rg.advanceWidthScale = 1.0;

        var mlgRegion = mlg.addRegion(rg);
        if (rg.envelope === 'arch') {
          mlgRegion.makeArch(rg.toparch, rg.bottomarch);
        }
        else if (rg.envelope === 'straight') {
          mlgRegion.makeStraightPaths();
        }
        else if (rg.envelope === 'radial-arch') {
          mlgRegion.makeRadialArch(rg.arch);
        }
      });

      staging.appendChild(mlg.render());

    });


}

function loadTemplates() {
  return fetch('templates.json')
    .then(response => response.json())
    .then(data => {
      templates = data;
      templates.forEach((template, templateIndex) => {
        let option = document.createElement('option');
        option.value = templateIndex;
        option.textContent = template.name;
        if (activeTemplateIndex == templateIndex) {
          option.selected = true;
        }
        mlgSelect.appendChild(option);
      });
    });
}

function emptySVG(svg) {
  let svgChildren = Array.from(svg.children);
  for (let child of svgChildren) {
    svg.removeChild(child);
  }
}
