import * as opentype from 'opentype.js';
import * as bezierWrapper from 'bezier-js';
import papercut from './papercut.js';

const Bezier = bezierWrapper.default;
const epsilon = 0.0001;
const fontCache = {};

export {
  Bowlcut
};

function Bowlcut(options = {}) {
  const wordmark = {
    text: [],
    colors: [],
    regions: [],
    fonts: [],
    precision: options.precision || 2,
    lutResolution: options.lutResolution || 100, //number of points in look up tables for curves
    debug: options.debug || false,
    uniqueId: Math.round(Math.random() * 1024).toString(16),
    fudgeFactor: 1.362, // not sure why this works - seems to be a good average for scaling fonts between paths
    // methods
    addRegion,
    removeRegion,
    render,
    loadFonts
  };

  Object.assign(wordmark, options);

  /**
   * addRegion creates and adds a region to a Bowlcut object
   * @param {Object} regionOptions allow for overrides for fill, stroke, etc. to be passed in on construction of a region.
   * @returns {Object} the region object
   */
  function addRegion(regionOptions) {
    //region constructor

    var region = {
      bounds: {
        x: 0,
        y: 0,
        width: 0,
        height: 0
      },
      topPath: null,
      bottomPath: null,
      stretchToWidth: false,
      font: 0,
      advanceWidthScale: 1,
      fill: null,
      stroke: null,
      slice: {
        0: []
      },
      debugPoints: [],
      uniqueId: Math.round(Math.random() * 1024).toString(16),
      // methods
      fitTextInBounds,
      renderRegion,
      makeStraightPaths,
      makeArch,
      makeRadialArch
    };

    Object.assign(region, regionOptions || {});
    wordmark.regions.push(region);
    return region;

    /**
     * fitTextInBounds scales the region's text to fit inside the region's bounds, with no other transformations
     * @returns {Object} the scaled text as an opentype Path
     */
    function fitTextInBounds() {
      let regionFont = wordmark.fonts[region.font];
      if (!regionFont) {
        console.error('Font file is not loaded for Bowlcut ' + wordmark.uniqueId);
        return;
      }

      let fontSize = region.bounds.height * wordmark.fudgeFactor;
      let regionText = '';

      //build region text string
      for (let textIndex in region.slice) {
        if (region.slice[textIndex].length) {
          regionText += wordmark.text[textIndex].slice.apply(wordmark.text[textIndex], region.slice[textIndex]);
        }
        else {
          regionText += wordmark.text[textIndex];
        }
      }

      // if the advanceWidthScale is modified, apply it to the font glyphs
      if (region.advanceWidthScale !== 1) {
        for (let glyphIndex = 0; glyphIndex < regionFont.glyphs.length; glyphIndex++) {
          let glyph = regionFont.glyphs.glyphs[glyphIndex];
          glyph.advanceWidth *= region.advanceWidthScale;
        }
      }

      let textPath = regionFont.getPath(regionText,0,0,fontSize);
      let textPathBounds = getPathElemBounds(parsePathElement(textPath,2));

      //undo our changes to the font for other regions
      if (region.advanceWidthScale !== 1) {
        for (let glyphIndex = 0; glyphIndex < regionFont.glyphs.length; glyphIndex++) {
          let glyph = regionFont.glyphs.glyphs[glyphIndex];
          glyph.advanceWidth /= region.advanceWidthScale;
        }
      }

      // Scale to fit bounds vertically
      // If width > bounds width, squish to fit
      // If stretchToWidth is active and width < bounds.width, fit bounds horizontally as well

      let widthScale = 1;
      if (region.stretchToWidth || (textPathBounds.width > region.bounds.width)) {
        widthScale = region.bounds.width / textPathBounds.width;
      }

      let heightScale = (region.bounds.height / textPathBounds.height);
      scaleOpenPath(textPath, widthScale, heightScale);

      //update the bounds again
      textPathBounds = getPathElemBounds(parsePathElement(textPath,2));

      //center the scaled text
      let nx = region.bounds.x + region.bounds.width / 2 - textPathBounds.width / 2 - textPathBounds.x;
      let ny = region.bounds.y - textPathBounds.y;

      translateOpenPath(textPath, nx, ny);
      reducePathToLines(textPath, Math.pow(10, wordmark.precision));
      return textPath;
    }

    /**
     * renderRegion uses the provided bounds and top/bottom paths for a region to render an SVG path in between
     * @returns {Object} the rendered SVGPathElement
     */
    function renderRegion() {
      //calls renderTextToBounds and then renders text between paths. returns opentype path

      let straightTextRegion = region.fitTextInBounds();
      let topPathLength = region.topPath.getTotalLength();
      let bottomPathLength = region.bottomPath.getTotalLength();
      let step = wordmark.lutResolution;
      let topPathLUT = [];
      let bottomPathLUT = [];
      let topPathBounds = getPathElemBounds(region.topPath);
      let bottomPathBounds = getPathElemBounds(region.bottomPath);

      if (wordmark.debug) {
        region.debugPoints = [];
      }

      for (let i = 0; i < step + 1; i++) {
        topPathLUT.push(region.topPath.getPointAtLength(topPathLength * i / step));
        bottomPathLUT.push(region.bottomPath.getPointAtLength(bottomPathLength * i / step));

        if (wordmark.debug) {
          region.debugPoints.push(topPathLUT[topPathLUT.length - 1]);
          region.debugPoints.push(bottomPathLUT[bottomPathLUT.length - 1]);
        }
      }

      if (Math.abs(topPathBounds.width - bottomPathBounds.width) < epsilon && Math.abs(topPathBounds.x - bottomPathBounds.x) < epsilon) {
        //assuming similar widths and left positions ~= no horizontal distortion
        straightTextRegion.commands.forEach((cmd) => {
          if ('ML'.indexOf(cmd.type) > -1) {

            for (let j = 0; j < step - 1; j++) {
              let sampleTopA = topPathLUT[j];
              let sampleTopB = topPathLUT[j + 1];

              if ((cmd.x <= sampleTopB.x && cmd.x >= sampleTopA.x) || (j >= step - 2 && cmd.x >= sampleTopB.x)) {

                let topLerpY = lerp(sampleTopA.y, sampleTopB.y, (cmd.x - sampleTopA.x) / (sampleTopB.x - sampleTopA.x));
                //found closest top, now let's find closest bottom
                for (let k = 0; k < step - 1; k++) {
                  let sampleBottomA = bottomPathLUT[k];
                  let sampleBottomB = bottomPathLUT[k + 1];

                  if ((cmd.x <= sampleBottomB.x && cmd.x >= sampleBottomA.x) || (k >= step - 2 && cmd.x >= sampleBottomB.x)) {
                    let bottomLerpY = lerp(sampleBottomA.y, sampleBottomB.y, (cmd.x - sampleBottomA.x) / (sampleBottomB.x - sampleBottomA.x));
                    let yProportional = (cmd.y - region.bounds.y) / region.bounds.height; //don't forget cmd is scaled already
                    cmd.y = lerp(topLerpY, bottomLerpY, yProportional);
                    j = k = step;
                  }
                }
              }
            }
          }
        });
      }
      else {
        straightTextRegion.commands.forEach((cmd) => {
          if ('ML'.indexOf(cmd.type) > -1) {
            let xProgress = (cmd.x - region.bounds.x) / region.bounds.width;
            let yProgress = (cmd.y - region.bounds.y) / region.bounds.height;

            let stepProgressX = (step) * xProgress;
            let floorStepProgressX = Math.max(0,Math.floor(stepProgressX));
            let ceilStepProgressX = Math.min(step, Math.ceil(stepProgressX));

            let topMinPt = topPathLUT[floorStepProgressX];
            let topMaxPt = topPathLUT[ceilStepProgressX];

            let bottomMinPt = bottomPathLUT[floorStepProgressX];
            let bottomMaxPt = bottomPathLUT[ceilStepProgressX];

            let progressRatio = (stepProgressX - floorStepProgressX) / (ceilStepProgressX - floorStepProgressX + epsilon);

            let topPt = {
              x: lerp(topMinPt.x, topMaxPt.x, progressRatio),
              y: lerp(topMinPt.y, topMaxPt.y, progressRatio)
            };

            let bottomPt = {
              x: lerp(bottomMinPt.x, bottomMaxPt.x, progressRatio),
              y: lerp(bottomMinPt.y, bottomMaxPt.y, progressRatio)
            };

            let lerpX = lerp(topPt.x,bottomPt.x, yProgress);
            let lerpY = lerp(topPt.y,bottomPt.y, yProgress);

            cmd.x = lerpX;
            cmd.y = lerpY;

          }
        });
      }

      let newPathToAppend = createSVGElement('path');
      newPathToAppend.setAttribute('d', straightTextRegion.toPathData(wordmark.precision));
      if (region.fill >= 0 && region.fill !== null) {
        newPathToAppend.setAttribute('fill', wordmark.colors[region.fill]);
      }
      else {
        newPathToAppend.setAttribute('fill', 'none');
      }
      if (region.stroke >= 0 && region.stroke !== null) {
        newPathToAppend.setAttribute('stroke', wordmark.colors[region.stroke]);
      }
      else {
        newPathToAppend.setAttribute('stroke', 'none');
      }
      newPathToAppend.setAttribute('stroke-width', region.bounds.height / 40);
      newPathToAppend.setAttribute('stroke-linejoin', 'round');
      newPathToAppend.setAttribute('stroke-linecap', 'round');

      return newPathToAppend;
    }

    /**
     * makeStraightPaths makes top and bottom paths from the verical edges of the region bounds
     */
    function makeStraightPaths() {
      let toparc = createSVGElement('path');
      let bottomarc = createSVGElement('path');
      toparc.setAttribute('d', 'M' + (region.bounds.x) + ',' + (region.bounds.y) + ' L' + (region.bounds.x + region.bounds.width) + ',' + (region.bounds.y));
      bottomarc.setAttribute('d', 'M' + (region.bounds.x) + ',' + (region.bounds.y + region.bounds.height) + ' L' + (region.bounds.x + region.bounds.width) + ',' + (region.bounds.y + region.bounds.height));
      region.topPath = toparc;
      region.bottomPath = bottomarc;
    }

    /**
     * makeArch makes quadratic arcs for the top and bottom path of a region
     * @param {Number} topBend can be positive or negative
     * @param {Number} bottomBend can be positive or negative
     */
    function makeArch(topBend, bottomBend) {
      let toparc = createSVGElement('path');
      let bottomarc = createSVGElement('path');
      let bottomarcstr = '';
      let toparcstr = '';
      let arcMultiplier = 2;
      let toparchstrength = topBend || 0;
      let bottomarchstrength = bottomBend || 0;

      let topquad = {
        x0: region.bounds.x,
        y0: region.bounds.y,
        x1: (region.bounds.x + region.bounds.width / 2),
        y1: (region.bounds.y - region.bounds.height * toparchstrength * arcMultiplier),
        x2: (region.bounds.x + region.bounds.width),
        y2: (region.bounds.y)
      };

      let bottomquad = {
        x0: region.bounds.x,
        y0: (region.bounds.y + region.bounds.height),
        x1: (region.bounds.x + region.bounds.width / 2),
        y1: (region.bounds.y + region.bounds.height - region.bounds.height * bottomarchstrength * arcMultiplier),
        x2: (region.bounds.x + region.bounds.width),
        y2: (region.bounds.y + region.bounds.height)
      };

      toparcstr += 'M' + topquad.x0 + ',' + topquad.y0 + ' ';
      toparcstr += 'Q';
      toparcstr += topquad.x1 + ',' + topquad.y1 + ' ';
      toparcstr += topquad.x2 + ',' + topquad.y2;
      toparc.setAttribute('d', toparcstr);

      bottomarcstr += 'M' + bottomquad.x0 + ',' + bottomquad.y0 + ' ';
      bottomarcstr += 'Q';
      bottomarcstr += bottomquad.x1 + ',' + bottomquad.y1 + ' ';
      bottomarcstr += bottomquad.x2 + ',' + bottomquad.y2;
      bottomarc.setAttribute('d', bottomarcstr);

      region.topPath = toparc;
      region.bottomPath = bottomarc;
    }

    /**
     * makeRadialArch sets the region's paths to a rainbow-shaped arch from the bounds and a bend strength
     * @param {Number} radialBend must be >= 0
     */
    function makeRadialArch(radialBend) {
      if (radialBend === 0) {
        return makeStraightPaths();
      }

      let toparc = createSVGElement('path');
      let bottomarc = createSVGElement('path');
      let bottomarcstr = '';
      let toparcstr = '';
      let arcBend = -(1 - radialBend) * Math.PI / 4;

      let arc = {
        r: 0, //radians
        theta: null,
        rc: 0,
        rg: region.bounds.width,
        px: (region.bounds.x + region.bounds.width / 2),
        py: (region.bounds.y + region.bounds.height),
        s: 0
      };

      calcArc(arcBend);
      drawArcs();
      region.topPath = toparc;
      region.bottomPath = bottomarc;

      function calcArc(newR) {
        arc.r = newR;
        arc.theta = Math.PI - 2 * newR;
        arc.rc = Math.sin(arc.r) / (arc.rg * Math.sin(arc.theta) + epsilon);
        arc.s = Math.tan(arc.theta) * arc.rg / 2;
      }

      function drawArcs() {
        let smallAx = region.bounds.x;
        let smallAy = (region.bounds.y + region.bounds.height);
        let smallBx = (region.bounds.x + region.bounds.width);
        let smallBy = smallAy;
        let smallRadius = Math.sqrt(Math.pow(arc.s,2) + Math.pow(region.bounds.width / 2,2));

        bottomarcstr = 'M' + smallAx + ' ' + smallAy;
        bottomarcstr += ' A' + smallRadius + ' ' + smallRadius + ' 0 0 1 ';
        bottomarcstr += smallBx + ' ' + smallBy;
        bottomarc.setAttribute('d', bottomarcstr);

        let bigAx = region.bounds.x + region.bounds.height * Math.cos(arc.theta);
        let bigAy = region.bounds.y + region.bounds.height + region.bounds.height * Math.sin(arc.theta);
        let bigBx = region.bounds.x + region.bounds.width - region.bounds.height * Math.cos(arc.theta);
        let bigBy = region.bounds.y + region.bounds.height + region.bounds.height * Math.sin(arc.theta);
        let bigRadius = smallRadius + region.bounds.height;

        toparcstr = 'M' + (bigAx) + ' ' + (bigAy);
        toparcstr += ' A' + bigRadius + ' ' + bigRadius + ' 0 0 1 ';
        toparcstr += bigBx + ' ' + bigBy;
        toparc.setAttribute('d', toparcstr);
      }
    }
  }

  /**
   * removeRegion deletes a region from a Bowlcut wordmark
   * @param {Object} region the region to delete
   */
  function removeRegion(region) {
    let regionIndex = wordmark.regions.findIndex((someRegion) => {
      return someRegion.uniqueId == region.uniqueId;
    });

    if (regionIndex > -1) {
      wordmark.regions.splice(regionIndex, 1);
    }
    else {
      console.error('Couldn\'t find region to delete.');
    }
  }

  /**
   * render creates an SVGGroupElement containing the rendered region paths
   * @param {Boolean} [unify] merges region paths with a union operation, removing overlaps. Expensive so defaults to false.
   * @returns {Object} the group element
   */
  function render(unify = false) {
    let wordmarkGroup = createSVGElement('g');
    wordmarkGroup.setAttribute('class', 'bowlcut-' + wordmark.uniqueId);
    wordmark.regions.forEach((region) => {
      wordmarkGroup.appendChild(region.renderRegion());
    });

    if (unify) {
      wordmarkGroup = papercut(wordmarkGroup);
    }

    if (wordmark.debug) {
      wordmark.regions.forEach((region) => {
        region.topPath.setAttribute('stroke', 'red');
        region.bottomPath.setAttribute('stroke', 'red');
        region.topPath.setAttribute('fill', 'none');
        region.bottomPath.setAttribute('fill', 'none');
        wordmarkGroup.appendChild(region.topPath);
        wordmarkGroup.appendChild(region.bottomPath);
        for (let debugPtIndex in region.debugPoints) {
          let ptData = region.debugPoints[debugPtIndex];
          let upPt = createSVGElement('circle');
          upPt.setAttribute('cx',ptData.x);
          upPt.setAttribute('cy',ptData.y);
          upPt.setAttribute('r',2);
          upPt.setAttribute('fill','#00ff00');
          wordmarkGroup.appendChild(upPt);
        }
      });
    }

    return wordmarkGroup;
  }

  /**
   * loadFonts takes an array of tuples like so: [[fontName, fontUrl], ...]]
   * @param {Array} fontTuples
   * @returns {Object} a promise resolved when the fonts have loaded
   */
  function loadFonts(fontTuples) {
    let fontPromises = [];

    fontTuples.map((fontTuple) => {
      let fontName = fontTuple[0];
      let fontUrl = fontTuple[1];

      fontPromises.push(new Promise((res, rej) => {
        if (typeof fontCache[fontName] !== 'undefined') {
          res(fontCache[fontName]);
          return;
        }

        opentype.load(fontUrl, (err, font) => {
          if (err) {
            rej(err);
            return;
          }
          res(font);
          fontCache[fontName] = font;
        });
      }));
    });

    return Promise.all(fontPromises)
      .then(fonts => {
        wordmark.fonts = fonts;
      })
      .catch(err => {
        throw new Error(err);
      });
  }

  return wordmark;
}

//path and math functions

function createSVGElement(elem) {
  return document.createElementNS('http://www.w3.org/2000/svg', elem);
}

function copyCommands(srcPath, destPath) {
  for (let cmdIndex in srcPath.commands) {
    let cmd = srcPath.commands[cmdIndex];
    let newCmd = {};
    let cmdKeys = Object.keys(cmd);
    for (let keyIndex in cmdKeys) {
      //deep copy values
      newCmd[cmdKeys[keyIndex]] = cmd[cmdKeys[keyIndex]];
    }
    destPath.commands.push(newCmd);
  }
}

function parsePathElement(pathElem, precision) {
  //returns a DOM node from the string
  let pathNode = createSVGElement('path');
  let openPathCopy = new opentype.Path();
  copyCommands(pathElem, openPathCopy);
  //quick and dirty sample count, a better method would be this:
  // http://www.antigrain.com/research12/adaptive_bezier/index.html
  reducePathToLines(openPathCopy, Math.pow(10, precision));
  pathNode.setAttribute('d', openPathCopy.toPathData(precision));
  return pathNode;
}

function getPathElemBounds(tPath) {
  let tempSvg = createSVGElement('svg');
  document.body.appendChild(tempSvg);
  tempSvg.appendChild(tPath);
  let tBounds = tPath.getBBox();
  document.body.removeChild(tempSvg);
  return tBounds;
}

function convertCommandToBezier(startX, startY, cmd) {
  let cmdHandler = {
    M: function() {
      return null; //not representable as a bezier
    },
    L: function() {
      let halfX = startX + (cmd.x - startX) / 2;
      let halfY = startY + (cmd.y - startY) / 2;
      return new Bezier(startX, startY, halfX, halfY, cmd.x, cmd.y);
    },
    C: function() {
      return new Bezier(startX, startY, cmd.x1, cmd.y1, cmd.x2, cmd.y2, cmd.x, cmd.y);
    },
    Q: function() {
      return new Bezier(startX, startY, cmd.x1, cmd.y1, cmd.x, cmd.y);
    },
    Z: function() {
      return null; //not representable as a bezier
    }
  };
  return cmdHandler[cmd.type](cmd);
}

function pointOnCubicBezier(points, t) {
  if (points.length == 1) {
    return points[0];
  }
  else {
    let newpoints = [];
    for (let i = 0; i < points.length - 1; i++) {
      let newpt = {};
      newpt.x = (1 - t) * points[i].x + t * points[i + 1].x;
      newpt.y = (1 - t) * points[i].y + t * points[i + 1].y;
      newpoints.push(newpt);
    }
    return pointOnCubicBezier(newpoints,t);
  }
}

function reducePathToLines(openPath, maxCurvePts) {
  let activeX = 0,
    activeY = 0,
    finalCommandList = [];

  let cmdHandler = {
    M: function(cmd) {
      activeX = cmd.x;
      activeY = cmd.y;
      finalCommandList.push(cmd);
    },
    L: function(cmd) {
      let cmdLength = measureCommandLength(activeX, activeY, cmd);
      let numSteps = Math.min(cmdLength, maxCurvePts);
      for (let i = 0; i < numSteps; i++) {
        let midX = lerp(activeX, cmd.x, i / numSteps);
        let midY = lerp(activeY, cmd.y, i / numSteps);
        finalCommandList.push({type: 'L', x: midX, y: midY});
        activeX = midX;
        activeY = midY;
      }
    },
    C: function(cmd) {
      let curvePoints = [
        {x: activeX, y: activeY},
        {x: cmd.x1, y: cmd.y1},
        {x: cmd.x2, y: cmd.y2},
        {x: cmd.x, y: cmd.y}
      ];
      let cmdLength = measureCommandLength(activeX, activeY, cmd);
      let numSteps = Math.min(cmdLength, maxCurvePts);
      for (let i = 0; i < numSteps; i++) {
        let newPt = pointOnCubicBezier(curvePoints, i / numSteps);
        let newCmd = {type: 'L', x: newPt.x, y: newPt.y};
        activeX = newCmd.x;
        activeY = newCmd.y;
        finalCommandList.push(newCmd);
      }
    },
    Q: function(cmd) {
      //converts quadratic curves to cubic
      return cmdHandler.C({
        type: 'C',
        x1: activeX + 2 / 3 * (cmd.x1 - activeX),
        y1: activeY + 2 / 3 * (cmd.y1 - activeY),
        x2: cmd.x + 2 / 3 * (cmd.x1 - cmd.x),
        y2: cmd.y + 2 / 3 * (cmd.y1 - cmd.y),
        x: cmd.x,
        y: cmd.y
      });
    },
    Z: function(cmd) {
      finalCommandList.push(cmd);
    }
  };

  openPath.commands.forEach((cmd) => {
    cmdHandler[cmd.type](cmd);
  });

  openPath.commands = finalCommandList;
  return openPath;
}

function scaleOpenPath(openPath,sx,sy) {
  openPath.commands.forEach((cmd) => {
    if ('ML'.indexOf(cmd.type) > -1) {
      cmd.x *= sx;
      cmd.y *= sy;
    }
    else if (cmd.type === 'C') {
      cmd.x *= sx;
      cmd.y *= sy;
      cmd.x1 *= sx;
      cmd.y1 *= sy;
      cmd.x2 *= sx;
      cmd.y2 *= sy;
    }
    else if (cmd.type === 'Q') {
      cmd.x *= sx;
      cmd.y *= sy;
      cmd.x1 *= sx;
      cmd.y1 *= sy;
    }
  });
}

function translateOpenPath(openPath,sx,sy) {
  openPath.commands.forEach((cmd) => {
    if ('ML'.indexOf(cmd.type) > -1) {
      cmd.x += sx;
      cmd.y += sy;
    }
    else if (cmd.type === 'C') {
      cmd.x += sx;
      cmd.y += sy;
      cmd.x1 += sx;
      cmd.y1 += sy;
      cmd.x2 += sx;
      cmd.y2 += sy;
    }
    else if (cmd.type === 'Q') {
      cmd.x += sx;
      cmd.y += sy;
      cmd.x1 += sx;
      cmd.y1 += sy;
    }
  });
}

function measureCommandLength(startX, startY, cmd) {
  if (cmd.type === 'M' || cmd.type === 'Z') {
    return 0;
  }
  else {
    let cmdBezier = convertCommandToBezier(startX, startY, cmd);
    if (cmdBezier !== null) {
      return cmdBezier.length();
    }
    else {
      console.error('tried to measure weird command:', cmd);
    }
  }
}

function lerp(a, b, t) {
  return (1 - t) * a + t * b;
}
