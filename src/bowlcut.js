(function(console, opentype, Bezier){

  'use strict';

    /*
      Bowlcut.JS - A library for generating warped SVG text
      hypothete 2015-17
    */

  window.Bowlcut = function(){
    var wordmark = {
      text: [],
      colors: [],
      regions: [],
      fonts: [],
      precision: 3,
      lutResolution: 100, //number of points in look up tables for curves
      debug: false,
      uniqueId: Math.round(Math.random()*1024).toString(16),
      addRegion: addRegion,
      render: render
    };

    function addRegion(regionOptions){
      //region constructor

      var region = {
        bounds : regionOptions.bounds || {
          x: 0,
          y: 0,
          width: 0,
          height: 0
        },
        topPath: regionOptions.topPath || null,
        bottomPath: regionOptions.bottomPath || null,
        stretchToWidth: regionOptions.stretchToWidth || false,
        font: regionOptions.font || 0,
        advanceWidthScale: regionOptions.advanceWidthScale || 1,
        fill: regionOptions.fill === 0 ? 0 : (regionOptions.fill || null),
        stroke: regionOptions.stroke === 0 ? 0 : (regionOptions.stroke || null),
        slice: regionOptions.slice || {
          0: []
        },
        debugPoints: [],

        // methods
        fitTextInBounds: fitTextInBounds,
        render: render,
        makeStraightPaths: makeStraightPaths,
        makeArch: makeArch,
        makeRadialArch: makeRadialArch
      };

      wordmark.regions.push(region);

      return region;

      function fitTextInBounds(){

        var regionFont = wordmark.fonts[region.font];
        if(!regionFont){
          console.error('Font file is not loaded for Bowlcut ' + wordmark.uniqueId);
          return;
        }

        var fontSize = region.bounds.height*1.362;
        var regionText = '';

        //build region text string
        for(var textIndex in region.slice){
          if(region.slice[textIndex].length){
            regionText += wordmark.text[textIndex].slice.apply(wordmark.text[textIndex], region.slice[textIndex]);
          }
          else{
            regionText += wordmark.text[textIndex];
          }
        }

        // if the advanceWidthScale is modified, apply it to the font glyphs
        if (region.advanceWidthScale !== 1) {
          for (var glyphIndex=0; glyphIndex < regionFont.glyphs.length; glyphIndex++) {
            var glyph = regionFont.glyphs.glyphs[glyphIndex];
            glyph.advanceWidth *= region.advanceWidthScale;
          }
        }

        var textPath = regionFont.getPath(regionText,0,0,fontSize);
        var textPathBounds = getPathElemBounds(parsePathElement(textPath,2));

        //undo our changes to the font for other regions
        if (region.advanceWidthScale !== 1) {
          for (var glyphIndex=0; glyphIndex < regionFont.glyphs.length; glyphIndex++) {
            var glyph = regionFont.glyphs.glyphs[glyphIndex];
            glyph.advanceWidth /= region.advanceWidthScale;
          }
        }

        // Scale to fit bounds vertically
        // If width > bounds width, squish to fit
        // If stretchToWidth is active and width < bounds.width, fit bounds horizontally as well

        var widthScale = 1;

        if(region.stretchToWidth || (textPathBounds.width > region.bounds.width)){
          widthScale = region.bounds.width/textPathBounds.width;
        }

        var heightScale = (region.bounds.height / textPathBounds.height);

        scaleOpenPath(textPath, widthScale, heightScale);

        //update the bounds again
        textPathBounds = getPathElemBounds(parsePathElement(textPath,2));

        //center the scaled text
        var nx = region.bounds.x + region.bounds.width/2 - textPathBounds.width/2 - textPathBounds.x;
        var ny = region.bounds.y - textPathBounds.y;

        translateOpenPath(textPath, nx, ny);

        reducePathToLines(textPath, Math.pow(5,wordmark.precision));

        return textPath;

      }

      function render(){
        //calls renderTextToBounds and then renders text between paths. returns opentype path

        var straightTextRegion = region.fitTextInBounds();
        var topPathLength = region.topPath.getTotalLength();
        var bottomPathLength = region.bottomPath.getTotalLength();
        var step = wordmark.lutResolution;
        var topPathLUT = [];
        var bottomPathLUT = [];
        var topPathBounds = getPathElemBounds(region.topPath);
        var bottomPathBounds = getPathElemBounds(region.bottomPath);
        var delta = 0.01;

        if(wordmark.debug){
          region.debugPoints = [];
        }

        for(var i=0; i<step+1; i++){
          topPathLUT.push(region.topPath.getPointAtLength(topPathLength*i/step));
          bottomPathLUT.push(region.bottomPath.getPointAtLength(bottomPathLength*i/step));

          if(wordmark.debug){
            region.debugPoints.push(topPathLUT[topPathLUT.length-1]);
            region.debugPoints.push(bottomPathLUT[bottomPathLUT.length-1]);
          }
        }

        if(Math.abs(topPathBounds.width -bottomPathBounds.width) < delta && Math.abs(topPathBounds.x - bottomPathBounds.x) < delta){
          //assuming similar widths and left positions ~= no horizontal distortion
          straightTextRegion.commands.forEach(function(cmd){
            if('ML'.indexOf(cmd.type) > -1){

              for(var j=0; j<step-1; j++){
                var sampleTopA = topPathLUT[j];
                var sampleTopB = topPathLUT[j+1];

                if((cmd.x <= sampleTopB.x && cmd.x >= sampleTopA.x) || (j >= step-2 && cmd.x >= sampleTopB.x)){

                  var topLerpY = lerp(sampleTopA.y, sampleTopB.y, (cmd.x - sampleTopA.x)/(sampleTopB.x - sampleTopA.x));
                  //found closest top, now let's find closest bottom
                  for(var k=0; k<step-1; k++){
                    var sampleBottomA = bottomPathLUT[k];
                    var sampleBottomB = bottomPathLUT[k+1];

                    if((cmd.x <= sampleBottomB.x && cmd.x >= sampleBottomA.x) || (k >= step-2 && cmd.x >= sampleBottomB.x)){
                      var bottomLerpY = lerp(sampleBottomA.y, sampleBottomB.y, (cmd.x - sampleBottomA.x)/(sampleBottomB.x - sampleBottomA.x));
                      var yProportional = (cmd.y - region.bounds.y)/region.bounds.height; //don't forget cmd is scaled already
                      cmd.y = lerp(topLerpY, bottomLerpY, yProportional);
                      j = k = step;
                    }
                  }
                }
              }
            }
          });
        }
        else{
          straightTextRegion.commands.forEach(function(cmd){
            if('ML'.indexOf(cmd.type) > -1){
              var xProgress = (cmd.x - region.bounds.x) / region.bounds.width;
              var yProgress = (cmd.y - region.bounds.y) / region.bounds.height;

              var stepProgressX = (step)*xProgress;
              var floorStepProgressX = Math.max(0,Math.floor(stepProgressX));
              var ceilStepProgressX = Math.min(step, Math.ceil(stepProgressX));

              var topMinPt = topPathLUT[floorStepProgressX];
              var topMaxPt = topPathLUT[ceilStepProgressX];

              var bottomMinPt = bottomPathLUT[floorStepProgressX];
              var bottomMaxPt = bottomPathLUT[ceilStepProgressX];

              var progressRatio = (stepProgressX - floorStepProgressX)/(ceilStepProgressX - floorStepProgressX + 0.0001);

              var topPt ={
                x: lerp(topMinPt.x, topMaxPt.x, progressRatio),
                y: lerp(topMinPt.y, topMaxPt.y, progressRatio)
              };

              var bottomPt ={
                x: lerp(bottomMinPt.x, bottomMaxPt.x, progressRatio),
                y: lerp(bottomMinPt.y, bottomMaxPt.y, progressRatio)
              };

              var lerpX = lerp(topPt.x,bottomPt.x, yProgress);
              var lerpY = lerp(topPt.y,bottomPt.y, yProgress);

              cmd.x = lerpX;
              cmd.y = lerpY;

            }
          });
        }

        var newPathToAppend = createSVGElement('path');
        newPathToAppend.setAttribute('d', straightTextRegion.toPathData(wordmark.precision));
        if(region.fill >= 0 && region.fill !== null) {
          newPathToAppend.setAttribute('fill', wordmark.colors[region.fill]);
        }
        else{
          newPathToAppend.setAttribute('fill', 'none');
        }
        if(region.stroke >= 0 && region.stroke !== null) {
          newPathToAppend.setAttribute('stroke', wordmark.colors[region.stroke]);
        }
        else{
          newPathToAppend.setAttribute('stroke', 'none');
        }
        newPathToAppend.setAttribute('stroke-width', region.bounds.height/40);
        newPathToAppend.setAttribute('stroke-linejoin', 'round');
        newPathToAppend.setAttribute('stroke-linecap', 'round');

        return newPathToAppend;
      }

      function makeStraightPaths(){
        var toparc = createSVGElement('path');
        var bottomarc = createSVGElement('path');
        toparc.setAttribute('d', 'M'+(region.bounds.x)+','+(region.bounds.y)+' L'+(region.bounds.x+region.bounds.width)+','+(region.bounds.y));
        bottomarc.setAttribute('d', 'M'+(region.bounds.x)+','+(region.bounds.y+region.bounds.height)+' L'+(region.bounds.x+region.bounds.width)+','+(region.bounds.y+region.bounds.height));
        region.topPath = toparc;
        region.bottomPath = bottomarc;
      }

      function makeArch(topBend, bottomBend){
        //sets topPath and bottomPath to quadratic arcs based on values
        var toparc = createSVGElement('path');
        var bottomarc = createSVGElement('path');
        var bottomarcstr = '';
        var toparcstr = '';
        var arcMultiplier = 2;
        var toparchstrength = topBend || 0;
        var bottomarchstrength = bottomBend || 0;

        var topquad = {
          x0: region.bounds.x,
          y0: region.bounds.y,
          x1: (region.bounds.x+region.bounds.width/2),
          y1: (region.bounds.y - region.bounds.height*toparchstrength*arcMultiplier),
          x2: (region.bounds.x+region.bounds.width),
          y2: (region.bounds.y)
        };

        var bottomquad = {
          x0: region.bounds.x,
          y0: (region.bounds.y+region.bounds.height),
          x1: (region.bounds.x+region.bounds.width/2),
          y1: (region.bounds.y+region.bounds.height - region.bounds.height*bottomarchstrength*arcMultiplier),
          x2: (region.bounds.x+region.bounds.width),
          y2: (region.bounds.y+region.bounds.height)
        };

        toparcstr += 'M'+ topquad.x0 + ',' + topquad.y0 + ' ';
        toparcstr += 'Q';
        toparcstr += topquad.x1 + ',' + topquad.y1 + ' ';
        toparcstr += topquad.x2 + ',' + topquad.y2;
        toparc.setAttribute('d', toparcstr);

        bottomarcstr += 'M'+ bottomquad.x0 + ',' + bottomquad.y0 + ' ';
        bottomarcstr += 'Q';
        bottomarcstr += bottomquad.x1 + ',' + bottomquad.y1 + ' ';
        bottomarcstr += bottomquad.x2 + ',' + bottomquad.y2;
        bottomarc.setAttribute('d', bottomarcstr);

        region.topPath = toparc;
        region.bottomPath = bottomarc;
      }

      function makeRadialArch(radialBend){
        //sets topPath and bottomPath to two radial arches

        if(radialBend === 0){
          return makeStraightPaths();
        }

        var toparc = document.createElementNS('http://www.w3.org/2000/svg', 'path');
        var bottomarc = document.createElementNS('http://www.w3.org/2000/svg', 'path');
        var bottomarcstr = '';
        var toparcstr = '';
        var arcBend = -(1-radialBend)*Math.PI/4;

        var arc = {
          r: 0, //radians
          theta: null,
          rc:0,
          rg: region.bounds.width,
          px: (region.bounds.x + region.bounds.width/2),
          py: (region.bounds.y + region.bounds.height),
          s: 0
        };

        calcArc(arcBend);
        drawArcs();
        region.topPath = toparc;
        region.bottomPath = bottomarc;

        function calcArc(newR){
          arc.r = newR;
          arc.theta = Math.PI - 2*newR;
          arc.rc = Math.sin(arc.r)/(arc.rg*Math.sin(arc.theta)+0.0001);
          arc.s = Math.tan(arc.theta)*arc.rg/2;
        }

        function drawArcs(){
          var smallAx = region.bounds.x;
          var smallAy = (region.bounds.y + region.bounds.height);
          var smallBx = (region.bounds.x+region.bounds.width);
          var smallBy = smallAy;
          var smallRadius = Math.sqrt(Math.pow(arc.s,2)+Math.pow(region.bounds.width/2,2));

          bottomarcstr = 'M'+ smallAx +' '+ smallAy;
          bottomarcstr += ' A' + smallRadius + ' ' + smallRadius + ' 0 0 1 ';
          bottomarcstr += smallBx + ' '+ smallBy;
          bottomarc.setAttribute('d', bottomarcstr);

          var bigAx = region.bounds.x + region.bounds.height*Math.cos(arc.theta);
          var bigAy = region.bounds.y + region.bounds.height + region.bounds.height*Math.sin(arc.theta);
          var bigBx = region.bounds.x + region.bounds.width - region.bounds.height*Math.cos(arc.theta);
          var bigBy = region.bounds.y + region.bounds.height + region.bounds.height*Math.sin(arc.theta);
          var bigRadius = smallRadius + region.bounds.height;

          toparcstr = 'M'+(bigAx)+' '+ (bigAy);
          toparcstr += ' A' + bigRadius + ' ' + bigRadius + ' 0 0 1 ';
          toparcstr += bigBx + ' '+ bigBy;
          toparc.setAttribute('d', toparcstr);
        }
      }
    }

    function render(){
      var wordmarkGroup = createSVGElement('g');
      wordmarkGroup.setAttribute('class', 'bowlcut-'+wordmark.uniqueId);
      wordmark.regions.forEach(function(region){
        wordmarkGroup.appendChild(region.render());
        if(wordmark.debug){
          region.topPath.setAttribute('stroke', 'red');
          region.bottomPath.setAttribute('stroke', 'red');
          region.topPath.setAttribute('fill', 'none');
          region.bottomPath.setAttribute('fill', 'none');
          wordmarkGroup.appendChild(region.topPath);
          wordmarkGroup.appendChild(region.bottomPath);
          for(var debugPtIndex in region.debugPoints){
            var ptData = region.debugPoints[debugPtIndex];
            var upPt = createSVGElement('circle');
            upPt.setAttribute('cx',ptData.x);
            upPt.setAttribute('cy',ptData.y);
            upPt.setAttribute('r',2);
            upPt.setAttribute('fill','#00ff00');
            wordmarkGroup.appendChild(upPt);
          }
        }
      });

      return wordmarkGroup;
    }

    return wordmark;
  };

  //path and math functions

  function createSVGElement(elem){
    return document.createElementNS('http://www.w3.org/2000/svg', elem);
  }

  function copyCommands(srcPath, destPath){
    for(var cmdIndex in srcPath.commands){
      var cmd = srcPath.commands[cmdIndex];
      var newCmd = {};
      var cmdKeys = Object.keys(cmd);
      for(var keyIndex in cmdKeys){
        //deep copy values
        newCmd[cmdKeys[keyIndex]] = cmd[cmdKeys[keyIndex]];
      }
      destPath.commands.push(newCmd);
    }
  }

  function parsePathElement(pathElem, precision){
    //returns a DOM node from the string
    var pathNode = createSVGElement('path');
    var openPathCopy = new opentype.Path();
    copyCommands(pathElem, openPathCopy);
    //quick and dirty sample count, a better method would be this:
    // http://www.antigrain.com/research12/adaptive_bezier/index.html
    reducePathToLines(openPathCopy, Math.pow(5,precision));
    pathNode.setAttribute('d', openPathCopy.toPathData(precision));
    return pathNode;
  }

  function getPathElemBounds(tPath){
    var tempSvg = createSVGElement('svg');
    document.body.appendChild(tempSvg);
    tempSvg.appendChild(tPath);
    var tBounds = tPath.getBBox();
    document.body.removeChild(tempSvg);
    return tBounds;
  }

  function convertCommandToBezier(startX, startY, cmd){
    var cmdHandler = {
      M: function(){
        return null; //not representable as a bezier
      },
      L: function(){
        var halfX = startX + (cmd.x - startX)/2;
        var halfY = startY + (cmd.y - startY)/2;
        return new Bezier(startX, startY, halfX, halfY, cmd.x, cmd.y);
      },
      C: function(){
        return new Bezier(startX, startY, cmd.x1, cmd.y1, cmd.x2, cmd.y2, cmd.x, cmd.y);
      },
      Q: function(){
        return new Bezier(startX, startY, cmd.x1, cmd.y1, cmd.x, cmd.y);
      },
      Z: function(){
        return null; //not representable as a bezier
      }
    };
    return cmdHandler[cmd.type](cmd);
  }

  function pointOnCubicBezier(points, t){
    if(points.length == 1) {
      return points[0];
    }
    else {
      var newpoints = [];
      for(var i=0; i<points.length-1; i++){
        var newpt = {};
        newpt.x = (1-t) * points[i].x + t * points[i+1].x;
        newpt.y = (1-t) * points[i].y + t * points[i+1].y;
        newpoints.push(newpt);
      }
      return pointOnCubicBezier(newpoints,t);
    }
  }

  function reducePathToLines(openPath, maxCurvePts){
    var activeX = 0,
      activeY = 0,
      finalCommandList = [];

    var cmdHandler = {
      M: function(cmd){
        activeX = cmd.x;
        activeY = cmd.y;
        finalCommandList.push(cmd);
      },
      L: function(cmd){
        var cmdLength = measureCommandLength(activeX, activeY, cmd);
        var numSteps = Math.min(cmdLength, maxCurvePts);
        for(var i=0; i<numSteps; i++){
          var midX = lerp(activeX, cmd.x, i/numSteps);
          var midY = lerp(activeY, cmd.y, i/numSteps);
          finalCommandList.push({type: 'L', x: midX, y: midY});
          activeX = midX;
          activeY = midY;
        }
      },
      C: function(cmd){
        var curvePoints = [
          {x: activeX, y: activeY},
          {x: cmd.x1, y: cmd.y1},
          {x: cmd.x2, y: cmd.y2},
          {x: cmd.x, y: cmd.y}
        ];
        var cmdLength = measureCommandLength(activeX, activeY, cmd);
        var numSteps = Math.min(cmdLength, maxCurvePts);

        for(var i=0; i<numSteps; i++){
          var newPt = pointOnCubicBezier(curvePoints, i/numSteps);
          var newCmd = {type: 'L', x: newPt.x, y: newPt.y};
          activeX = newCmd.x;
          activeY = newCmd.y;
          finalCommandList.push(newCmd);
        }
      },
      Q: function(cmd){
        //converts quadratic curves to cubic
        return cmdHandler.C({
          type: 'C',
          x1: activeX + 2/3 *(cmd.x1-activeX),
          y1: activeY + 2/3 *(cmd.y1-activeY),
          x2: cmd.x + 2/3 *(cmd.x1-cmd.x),
          y2: cmd.y + 2/3 *(cmd.y1-cmd.y),
          x:cmd.x,
          y:cmd.y
        });
      },
      Z: function(cmd){
        finalCommandList.push(cmd);
      }
    };

    openPath.commands.forEach(function(cmd){
      cmdHandler[cmd.type](cmd);
    });

    openPath.commands = finalCommandList;
    return openPath;
  }

  function scaleOpenPath(openPath,sx,sy){

    openPath.commands.forEach(function(cmd){
      if('ML'.indexOf(cmd.type) > -1){
        cmd.x *= sx;
        cmd.y *= sy;
      }
      else if(cmd.type === 'C'){
        cmd.x *= sx;
        cmd.y *= sy;
        cmd.x1 *= sx;
        cmd.y1 *= sy;
        cmd.x2 *= sx;
        cmd.y2 *= sy;
      }
      else if(cmd.type === 'Q'){
        cmd.x *= sx;
        cmd.y *= sy;
        cmd.x1 *= sx;
        cmd.y1 *= sy;
      }
    });
  }

  function translateOpenPath(openPath,sx,sy){
    openPath.commands.forEach(function(cmd){
      if('ML'.indexOf(cmd.type) > -1){
        cmd.x += sx;
        cmd.y += sy;
      }
      else if(cmd.type === 'C'){
        cmd.x += sx;
        cmd.y += sy;
        cmd.x1 += sx;
        cmd.y1 += sy;
        cmd.x2 += sx;
        cmd.y2 += sy;
      }
      else if(cmd.type === 'Q'){
        cmd.x += sx;
        cmd.y += sy;
        cmd.x1 += sx;
        cmd.y1 += sy;
      }
    });
  }

  function measureCommandLength(startX, startY, cmd){
    if(cmd.type === 'M' || cmd.type === 'Z'){
      return 0;
    }
    else{
      var cmdBezier = convertCommandToBezier(startX, startY, cmd);
      if(cmdBezier !== null){
        return cmdBezier.length();
      }
      else{
        console.error('tried to measure weird command:', cmd);
      }
    }
  }

  function lerp(a, b, t){
    return (1-t)*a + t*b;
  }

})(window.console, window.opentype, window.Bezier);
