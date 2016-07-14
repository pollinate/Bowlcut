(function(opentype){

	'use strict';

		/*
			BOWLCUT.JS
			v0.0.5
			A library for generating warped SVG text
			hypothete 2016
		*/

	window.Bowlcut = function(){
		var wordmark = {
			text: [],
			colors: [],
			regions: [],
			fonts: [],
			precision: 3,
			debug: true,
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
				topPath: null,
				bottomPath: null,
				font: regionOptions.font || 0,
				fill: regionOptions.fill === 0 ? 0 : (regionOptions.fill || null),
				stroke: regionOptions.stroke === 0 ? 0 : (regionOptions.stroke || null),
				slice: regionOptions.slice || {
					0: []
				},
				renderTextToBounds: renderTextToBounds,
				render: render,
				makeStraightPaths: makeStraightPaths,
				makeArch: makeArch,
				makeRadialArch: makeRadialArch
			};

			wordmark.regions.push(region);

			return region;

			function renderTextToBounds(){
				//returns text as an opentype path within the bounds

				var regionFont = wordmark.fonts[region.font];
				if(!regionFont){
					console.error('Font file is not loaded for Bowlcut ' + wordmark.uniqueId);
					return;
				}

				//build straight path at bottom of bounds
				var straightPath = createSVGElement('path');
				straightPath.setAttribute('d', 'M'+(region.bounds.x)+','+ (region.bounds.y+region.bounds.height)+
					' L'+(region.bounds.x+region.bounds.width)+','+(region.bounds.y+region.bounds.height));
				var fontSize = region.bounds.height*1.25;
				var straightPathLength = straightPath.getTotalLength();

				//build region text string
				var regionText = '';
				for(var textIndex in region.slice){
					if(region.slice[textIndex].length){
						regionText += wordmark.text[textIndex].slice.apply(wordmark.text[textIndex], region.slice[textIndex]);
					}
					else{
						regionText += wordmark.text[textIndex];
					}
				}

				var charPaths = [];
				var charGlyphs = [];
				var charAdvances = [];
				var charWidths = [];
				var kerningValues = [];
				var textWidth = getPathElemBounds(parsePathElement(regionFont.getPath(regionText,0,0,fontSize),2)).width;
				var finalPathCommands = [];
				var finalPath = new opentype.Path();

				for(var i=0; i<regionText.length; i++){
					charPaths[i] = regionFont.getPath(regionText.charAt(i),0,0,fontSize);
					reducePathToLines(charPaths[i], Math.pow(5,wordmark.precision));
					charGlyphs[i] = regionFont.charToGlyph(regionText.charAt(i));
					charAdvances[i] = fontSize * charGlyphs[i].advanceWidth / regionFont.unitsPerEm;
					if(charGlyphs[i].xMax){
						charWidths[i] = fontSize * (charGlyphs[i].xMax - charGlyphs[i].xMin) / regionFont.unitsPerEm;
					}
					else{
						charWidths[i] = getPathElemBounds(parsePathElement(charPaths[i],wordmark.precision)).width;
					}
				}

				if(regionText.length > 1){
					for(var i=0; i<regionText.length-1; i++){
						//second pass for kerns
						kerningValues[i] = fontSize * regionFont.getKerningValue(charGlyphs[i], charGlyphs[i+1]) / regionFont.unitsPerEm;
					}
				}

				//choose behavior based on path size

				if(textWidth > straightPathLength){
					//justify the text, squishing if necessary

					var advanceSum = charAdvances.reduce(function(a,b){
						return a+b;
					});
					var widthScale = straightPathLength/advanceSum;
					var currentPathOffset = 0;

					if(widthScale >= 1){
						//path is longer than rendered text, just spread out characters
						for(var j=0; j<regionText.length; j++){
							var pointOnPath = straightPath.getPointAtLength(currentPathOffset);
							if(j===0){
								placeGlyph(pointOnPath, currentPathOffset, charPaths[j], 0,0);
							}
							else{
								placeGlyph(pointOnPath, currentPathOffset, charPaths[j], charAdvances[j], charWidths[j]);
							}
							if(j < regionText.length-2){
								currentPathOffset += widthScale*(charAdvances[j]+kerningValues[j]);
							}
							else{
								currentPathOffset += widthScale*charAdvances[j];
							}
						}
					}
					else{
						//path is shorter than string, scale down chars to fit
						for(var j=0; j<regionText.length; j++){
							var pointOnPath = straightPath.getPointAtLength(currentPathOffset);
							scaleReducedPath(charPaths[j],widthScale, 1);
							charAdvances[j] *= widthScale;
							charWidths[j] *= widthScale;
							kerningValues[j] *= widthScale;

							if(j===0){
								placeGlyph(pointOnPath, currentPathOffset, charPaths[j], 0);
							}
							else{
								placeGlyph(pointOnPath, currentPathOffset, charPaths[j], charAdvances[j]);
							}
							if(j < regionText.length-1){
								currentPathOffset += charAdvances[j]+kerningValues[j];
							}
						}
					}
				}
				else{
					//center the text

					var positionOffset = straightPathLength/2 - textWidth/2;
					var currentCharOffset = 0;

					for(var j=0; j<regionText.length; j++){
						var lengthOnPath = positionOffset + currentCharOffset;
						var pointOnPath = straightPath.getPointAtLength(lengthOnPath);

						placeGlyph(pointOnPath, lengthOnPath, charPaths[j], charAdvances[j], charWidths[j]);

						if(j < regionText.length-1){
							currentCharOffset += charAdvances[j] + kerningValues[j];
						}
					}
				}

				function placeGlyph (pointA, lengthToPt, openPath){
					openPath.commands.forEach(function(pathCmd){
						if('ML'.indexOf(pathCmd.type)>-1){
							pathCmd.x = Number((pathCmd.x+pointA.x).toFixed(wordmark.precision));
							pathCmd.y = Number((pathCmd.y+pointA.y).toFixed(wordmark.precision));
						}
					});
				}

				charPaths.forEach(function(charPath){
					finalPathCommands = finalPathCommands.concat(charPath.commands);
				});

				finalPath.commands = finalPathCommands;

				return finalPath;
			}

			function render(){
				//calls renderTextToBounds and then renders text between paths. returns opentype path

				var straightTextRegion = region.renderTextToBounds();
				var topPathLength = region.topPath.getTotalLength();
				var bottomPathLength = region.bottomPath.getTotalLength();
				var step = 20;
				var topPathLUT = [];
				var bottomPathLUT = [];
				var topPathBounds = getPathElemBounds(region.topPath);
				var bottomPathBounds = getPathElemBounds(region.bottomPath);
				var delta = 0.01;

				for(var i=0; i<step; i++){
					topPathLUT.push(region.topPath.getPointAtLength(topPathLength*i/step));
					bottomPathLUT.push(region.bottomPath.getPointAtLength(bottomPathLength*i/step));
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

							var stepProgressX = (step-1)*xProgress;
							var floorStepProgressX = Math.floor(stepProgressX);
							var ceilStepProgressX = Math.ceil(stepProgressX);
							
							var topMinPt = topPathLUT[floorStepProgressX];
							var topMaxPt = topPathLUT[ceilStepProgressX];

							var bottomMinPt = bottomPathLUT[floorStepProgressX];
							var bottomMaxPt = bottomPathLUT[ceilStepProgressX];

							var progressRatio = (stepProgressX - floorStepProgressX)/(ceilStepProgressX - floorStepProgressX);

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
				newPathToAppend.setAttribute('fill', wordmark.colors[region.fill] || 'none');
				newPathToAppend.setAttribute('stroke', wordmark.colors[region.stroke] || 'none');
				newPathToAppend.setAttribute('stroke-width', region.bounds.height/40);
				
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
				//sets topPath and bottomPath to arches based on values
				var toparc = createSVGElement('path');
				var bottomarc = createSVGElement('path');
				var bottomarcstr = '';
				var toparcstr = '';
				var arcMultiplier = 1.325;
				var toparchstrength = topBend || 0;
				var bottomarchstrength = bottomBend || 0;

				var topcubic = {
					x0: region.bounds.x,
					y0: region.bounds.y,
					x1: region.bounds.x,
					y1: (region.bounds.y - region.bounds.height*toparchstrength*arcMultiplier),
					x2: (region.bounds.x+region.bounds.width),
					y2: (region.bounds.y - region.bounds.height*toparchstrength*arcMultiplier),
					x3: (region.bounds.x+region.bounds.width),
					y3: (region.bounds.y)
				};

				var bottomcubic = {
					x0: region.bounds.x,
					y0: (region.bounds.y+region.bounds.height),
					x1: region.bounds.x,
					y1: (region.bounds.y+region.bounds.height - region.bounds.height*bottomarchstrength*arcMultiplier),
					x2: (region.bounds.x+region.bounds.width),
					y2: (region.bounds.y+region.bounds.height - region.bounds.height*bottomarchstrength*arcMultiplier),
					x3: (region.bounds.x+region.bounds.width),
					y3: (region.bounds.y+region.bounds.height)
				};

				toparcstr += 'M'+ topcubic.x0 + ',' + topcubic.y0 + ' ';
				toparcstr += 'C';
				toparcstr += topcubic.x1 + ',' + topcubic.y1 + ' ';
				toparcstr += topcubic.x2 + ',' + topcubic.y2 + ' ';
				toparcstr += topcubic.x3 + ',' + topcubic.y3;
				toparc.setAttribute('d', toparcstr);

				bottomarcstr += 'M'+ bottomcubic.x0 + ',' + bottomcubic.y0 + ' ';
				bottomarcstr += 'C';
				bottomarcstr += bottomcubic.x1 + ',' + bottomcubic.y1 + ' ';
				bottomarcstr += bottomcubic.x2 + ',' + bottomcubic.y2 + ' ';
				bottomarcstr += bottomcubic.x3 + ',' + bottomcubic.y3;
				bottomarc.setAttribute('d', bottomarcstr);

				region.topPath = toparc;
				region.bottomPath = bottomarc;
			}

			function makeRadialArch(radialBend){
				//sets topPath and bottomPath to two radial arches

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
			wordmarkGroup.classList.add('bowlcut-'+wordmark.uniqueId);
			wordmark.regions.forEach(function(region){
				wordmarkGroup.appendChild(region.render());
				if(wordmark.debug){
					region.topPath.setAttribute('stroke', 'red');
					region.bottomPath.setAttribute('stroke', 'red');
					region.topPath.setAttribute('fill', 'none');
					region.bottomPath.setAttribute('fill', 'none');
					wordmarkGroup.appendChild(region.topPath);
					wordmarkGroup.appendChild(region.bottomPath);
				}
			});

			return wordmarkGroup;

			//merge regions or something
			//return merged result
		}

		return wordmark;
	};

	//path and math functions

	function createSVGElement(elem){
		return document.createElementNS('http://www.w3.org/2000/svg', elem);
	}

	function parsePathElement(pathElem, precision){
		//returns a DOM node from the string
		var pathNode = createSVGElement('path');
		//quick and dirty sample count, a better method would be this:
		// http://www.antigrain.com/research12/adaptive_bezier/index.html
		reducePathToLines(pathElem, Math.pow(5,precision));
		pathNode.setAttribute('d', pathElem.toPathData(precision));
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

	function scaleReducedPath(openPath,sx,sy){
		openPath.commands.forEach(function(cmd){
			if('ML'.indexOf(cmd.type) > -1){
				cmd.x *= sx;
				cmd.y *= sy;
			}
		});
	}

	function measureCommandLength(startX, startY, cmd){
		var pathString = 'M' + startX + ' ' + startY + ', ' + cmd.type;
		var pt1 = (cmd.x1? (cmd.x1 + ' ' + cmd.y1) : '');
		var pt2 = (cmd.x2? (cmd.x2 + ' ' + cmd.y2) : '');
		var ptEnd = cmd.x + ' ' + cmd.y;
		if(pt1.length){
			pathString += pt1 + ', ' + pt2 + ', ' + ptEnd;
		}
		else{
			pathString += ptEnd;
		}
		var pathElem = createSVGElement('path');
		pathElem.setAttribute('d', pathString);
		return pathElem.getTotalLength();
	}

	function lerp(a, b, t){
		return (1-t)*a + t*b;
	}

})(window.opentype);

