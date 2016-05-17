(function(){

	'use strict';

		/*
			BOWLCUT.JS
			v0.0.4
			A library for generating text on SVG paths
			outputs a group with styled & transformed text elements
			hypothete 2016
		*/

	var Bowlcut = {};

	Bowlcut.textBehaviors = [
		'center', //text is center-aligned on the path
		'left',
		'right',
		'justify', //text is evenly distributed along the path
	];

	Bowlcut.glyphBehaviors = [
		'tangent', //text width stays locked & glyph rotates to path's slope
		'upright' //glyph width stays locked & rotation is locked
	];

	Bowlcut.TextPath = function(){
		var textPath = {
			path: null,
			pathLength: -1,
			pathReverse: false,

			text: '',
			styles: {},
			attributes: {},

			minBehavior: Bowlcut.textBehaviors[0],
			maxBehavior: Bowlcut.textBehaviors[3],
			glyphBehavior: Bowlcut.glyphBehaviors[1],

			precision: 3,

			uniqueId: Math.round(Math.random()*1024).toString(16),
			font: null, //Opentype Font object

			setPath: function(element, reverse){
				//save the path & any metrics we need
				textPath.path = element;
				textPath.pathReverse = !!reverse;
				textPath.pathLength = element.getTotalLength();
				return textPath;
			},

			setPathFromCircle: function(x, y, r, reverse, flipText){
				textPath.path = createCirclePath(x,y,r, flipText);
				textPath.pathReverse = reverse;
				textPath.pathLength = textPath.path.getTotalLength();
				return textPath;
			},

			setPathFromArc: function(x, y, r, angle, upOrDown){
				var startAngle, endAngle;
				if(upOrDown === 'up'){
					startAngle = -angle/2;
					endAngle = angle/2;
					textPath.path = createArc(x,y,r,startAngle, endAngle,false);
					textPath.pathReverse = false;
				}
				else {
					startAngle = 180-angle/2;
					endAngle = 180+angle/2;
					textPath.path = createArc(x,y,r,startAngle, endAngle,true);
					textPath.pathReverse = true;
				}
				
				textPath.pathLength = textPath.path.getTotalLength();
				return textPath;
			},

			getPointOnPath: function(length){
				if(textPath.pathReverse) {
					return textPath.path.getPointAtLength(textPath.pathLength - length);
				}
				else {
					return textPath.path.getPointAtLength(length);
				}
			},

			render: function(){
				//returns a group node with positioned path elements

				if(!textPath.font){
					console.error('Font file is not loaded for path ' + textPath.uniqueId);
					return;
				}

				var textGroup = createSVGElement('g');
				textGroup.setAttribute('id', 'bowlcut-'+textPath.uniqueId);

				var charPaths = [],
					charPathElems = [],
					charGlyphs = [],
					charAdvances = [],
					kerningValues = [],
					fontSize = textPath.styles.fontSize || textPath.attributes.fontSize || 72,
					textWidth = 0;

				var glyphBehaviorAdjustments = {
					tangent: function(pointA, lengthToPt, charElem, charAdvance){
						var pointB = textPath.getPointOnPath(lengthToPt+charAdvance),
							secant = {
								x: pointB.x - pointA.x,
								y: pointB.y - pointA.y
							},
							normal = {x: -secant.y, y: secant.x},
							theta = Math.atan2(normal.y,normal.x)-Math.PI/2,
							angle = 180 * (theta)/Math.PI;

						charElem.setAttribute(
							'transform',
							'translate('+(pointA.x).toFixed(textPath.precision)+
							' '+(pointA.y).toFixed(textPath.precision)+
							') rotate('+(angle.toFixed(textPath.precision))+')');
					},
					upright: function(pointA, lengthToPt, charElem){
						charElem.setAttribute(
							'transform',
							'translate('+(pointA.x).toFixed(textPath.precision)+
							' '+(pointA.y).toFixed(textPath.precision)+
							')');
					}
				};

				var textBehaviorsToPlacements = {
					center: function(offset){
						var positionOffset = textPath.pathLength/2 - textWidth/2;
						var currentCharOffset = 0;
						if(offset && offset === 'left'){
							positionOffset = 0;
						}
						else if(offset && offset === 'right'){
							positionOffset = textPath.pathLength - textWidth;
						}

						for(var j=0; j<textPath.text.length; j++){
							var lengthOnPath = positionOffset + currentCharOffset;
							var pointOnPath = textPath.getPointOnPath(lengthOnPath);

							if(charPathElems[j].getAttribute('d').length){
								glyphBehaviorAdjustments[textPath.glyphBehavior](pointOnPath, lengthOnPath, charPathElems[j], charAdvances[j]);
								textGroup.appendChild(charPathElems[j]);
							}
							
							if(j < textPath.text.length-1){
								currentCharOffset += charAdvances[j] + kerningValues[j];
							}
						}
					},
					left: function(){
						textBehaviorsToPlacements.center('left');
					},
					right: function(){
						textBehaviorsToPlacements.center('right');
					},
					justify: function(){
						for(var j=0; j<textPath.text.length; j++){
							var currentCharOffset =  textPath.pathLength*j/textPath.text.length;
							var pointOnPath = textPath.getPointOnPath(currentCharOffset);
							glyphBehaviorAdjustments[textPath.glyphBehavior](pointOnPath, currentCharOffset, charPathElems[j], charAdvances[j]);
							textGroup.appendChild(charPathElems[j]);
						}
					}
				};

				for(var i=0; i<textPath.text.length; i++){
					charPaths[i] = textPath.font.getPath(textPath.text.charAt(i),0,0,fontSize);
					charPathElems[i] = parsePathElement(charPaths[i]);
					setAttributes(charPathElems[i], textPath.attributes);
					charGlyphs[i] = textPath.font.charToGlyph(textPath.text.charAt(i));
					charAdvances[i] = fontSize * charGlyphs[i].advanceWidth / textPath.font.unitsPerEm;
					//add advance width
					if(i > 0){
						textWidth += charAdvances[i];
					}
					//add kern for next char
					if(i>0){
						kerningValues[i-1] = fontSize * textPath.font.getKerningValue(charGlyphs[i-1], charGlyphs[i]) / textPath.font.unitsPerEm;
						textWidth += kerningValues[i-1];
					}
				}

				//choose behavior based on path size
				if(textWidth > textPath.pathLength){
					textBehaviorsToPlacements[textPath.maxBehavior]();
				}
				else{
					textBehaviorsToPlacements[textPath.minBehavior]();
				}

				return textGroup;
			}
		};

		return textPath;

		function createSVGElement(elem){
			return document.createElementNS('http://www.w3.org/2000/svg', elem);
		}

		function setAttributes(elem, attrObj){
			for(var attr in attrObj){
				elem.setAttribute(attr, attrObj[attr]);
			}
		}

		function createCirclePath(x,y,r, flipText){
			var path = createSVGElement('path'),
				d;
			if(!flipText){
				d = 'M'+(x)+','+(y+r)+ ' a'+r+','+r+' 0 0,1 0,'+(-r*2)+' a'+r+','+r+' 0 0,1 0,'+(r*2);
			}
			else{
				d = 'M'+(x)+','+(y-r)+ ' a'+r+','+r+' 0 0,0 0,'+(r*2)+' a'+r+','+r+' 0 0,0 0,'+(-r*2);
			}
			setAttributes(path, {
				d:  d,
				fill: 'none',
				stroke: 'black'
			});

			return path;
		}

		function createArc(x,y,r,startAngle, endAngle){
			var path = createSVGElement('path'),
				startPoint = polarToCartesian(x,y,r,startAngle),
				endPoint = polarToCartesian(x,y,r,endAngle),
				d = [
					'M', startPoint.x, startPoint.y,
					'a', r, r, 0, 0, 1, endPoint.x-startPoint.x, endPoint.y-startPoint.y
				].join(' ');

			setAttributes(path, {
				d:  d,
				fill: 'none',
				stroke: 'black'
			});

			return path;
		}

		function polarToCartesian(cx, cy, r, angle){
			//based off http://stackoverflow.com/questions/5736398/how-to-calculate-the-svg-path-for-an-arc-of-a-circle
			var angleToRads = (angle-90)*Math.PI/180,
				coords = {
					x: cx + r*Math.cos(angleToRads),
					y: cy + r*Math.sin(angleToRads)
				};
				return coords;
		}

		function parsePathElement(pathElem, precision){
			//returns a DOM node from the string
			var pathNode = createSVGElement('path');
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
	};

	window.Bowlcut = Bowlcut;

})();

