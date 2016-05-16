window.Bowlcut = function(){
	'use strict';

	/*
		BOWLCUT.JS
		v0.0.3
		A library for generating text on SVG paths
		outputs a group with styled & transformed text elements
		hypothete 2015
	*/

	var textBehaviors = [
			'center', //text is center-aligned on the path
			'left',
			'right',
			'justify', //text is evenly distributed along the path
		//	'flex-tracking', //text is justified with only whitespace stretched
		//	'pad-tracking' //text is justified, whitespace is distributed between inside the string and its beginning & end
		],

		glyphBehaviors = [
			'tangent', //text width stays locked & glyph rotates to path's slope
			'ribbon', //glyph stays upright, but becomes less wide with the slope
			'upright' //glyph width stays locked & rotation is locked
		],

		bowlcut = {
		//instance properties

		path: null,
		pathLength: -1,
		pathReverse: false,

		text: '',
		textAttributes: {},
		textStyles: {
			'text-anchor': 'middle'
		},
		textLength: -1,
		padding: 0,

		minBehavior: textBehaviors[3],
		maxBehavior: textBehaviors[3],
		glyphBehavior: glyphBehaviors[1],

		precision: 3,

		uniqueId: Math.round(Math.random()*1024).toString(16),

		//methods
		render: function(){
			//returns a group node with positioned text elements

			var textGroup = createSVGElement('g'),
				placements = [],
				glyphs = [],
				glyphWidths = [];

			textGroup.setAttribute('id', 'bowlcut-'+bowlcut.uniqueId);

			//determine positions
			var textBehaviorsToPlacements = {
				center: function(/*leftOrRight*/){
					var gradualTextLengths = [],
						pointOnPath,
						leftOrRight = arguments[0],
						fullTextLength = measureText(bowlcut.text);
					glyphs.forEach(function(gl, gInd){
						var partialString = bowlcut.text.slice(0,gInd+1),
							relativeGlyphPosition,
							glyphLengthOnPath,
							halfGlyphWidth = (glyphWidths[gInd]  + bowlcut.padding)/2,
							textLengthBeforeGlyph = (gInd > 0? gradualTextLengths[gInd-1] : 0) + halfGlyphWidth;
						gradualTextLengths.push(measureText(partialString));

						if(leftOrRight === undefined){
							relativeGlyphPosition = textLengthBeforeGlyph-0.5*fullTextLength;
							glyphLengthOnPath = bowlcut.pathLength/2 + relativeGlyphPosition;
						}
						else if(leftOrRight === 'left'){
							relativeGlyphPosition = textLengthBeforeGlyph;
							glyphLengthOnPath = relativeGlyphPosition;
						}
						else if(leftOrRight === 'right'){
							relativeGlyphPosition = textLengthBeforeGlyph-fullTextLength;
							glyphLengthOnPath = bowlcut.pathLength + relativeGlyphPosition;
						}
						pointOnPath = bowlcut.get.pointOnPath(glyphLengthOnPath);
						textGroup.appendChild(gl);
						setAttributes(gl,{x: pointOnPath.x.toFixed(bowlcut.precision), y: pointOnPath.y.toFixed(bowlcut.precision)});
						glyphBehaviorAdjustments[bowlcut.glyphBehavior](gl, bowlcut.pathReverse? (bowlcut.pathLength - glyphLengthOnPath) : glyphLengthOnPath, gInd);
					});
				},
				left: function(){
					textBehaviorsToPlacements.center('left');
				},
				right: function(){
					textBehaviorsToPlacements.center('right');
				},
				justify: function(){
					glyphs.forEach(function(gl, gInd){
						var lengthToGlyph = bowlcut.pathLength*(gInd/(glyphs.length-1)),
						pointOnPath = bowlcut.get.pointOnPath(lengthToGlyph);
						textGroup.appendChild(gl);
						setAttributes(gl,{x: pointOnPath.x.toFixed(bowlcut.precision), y: pointOnPath.y.toFixed(bowlcut.precision)});
						glyphBehaviorAdjustments[bowlcut.glyphBehavior](gl, bowlcut.pathReverse? (bowlcut.pathLength - lengthToGlyph) : lengthToGlyph, gInd);
					});
				}
				// ,
				// 'flex-tracking': function(){
				// 	var words = bowlcut.text.trim().split(/\s+/g);
				// 	console.log(words);
				// 	// glyphs.forEach(function(glyph, glIndex){

				// 	// });

				// },
				// 'pad-tracking': function(){

				// }
			};

			var glyphBehaviorAdjustments = {
				tangent: function(glyphElem, glyphLength){
					var pointA = bowlcut.path.getPointAtLength(Math.max(0, glyphLength-1)), //not adjusted on pathReverse, incoming metric is
						pointB = bowlcut.path.getPointAtLength(glyphLength+1),
						secant = {
							x: pointB.x - pointA.x,
							y: pointB.y - pointA.y
						},
						normal = {x: -secant.y, y: secant.x},
						theta = Math.atan2(normal.y,normal.x)-Math.PI/2,
						angle = 180 * (theta)/Math.PI;

					if(bowlcut.pathReverse){
						angle -= 180;
					}
					glyphElem.setAttribute('transform', 'rotate('+angle.toFixed(bowlcut.precision)+' '+pointA.x.toFixed(bowlcut.precision)+' '+pointA.y.toFixed(bowlcut.precision)+')');
				},
				ribbon: function(glyphElem, glyphLength, glInd){
					var pointA = bowlcut.path.getPointAtLength(glyphLength-0.01),
						pointB = bowlcut.path.getPointAtLength(glyphLength+0.01),
						dPath = {x: pointB.x - pointA.x, y: pointB.y- pointA.y},
						dot = dotProduct(normalize(dPath), {x:1, y:0}) || 0.01; //revisit for NaNs
					glyphElem.setAttribute('textLength', Math.abs(glyphWidths[glInd]*dot).toFixed(bowlcut.precision));
					glyphElem.setAttribute('lengthAdjust', 'spacingAndGlyphs');
				},
				upright: function(){
					return; //nothing to see here
				}
			};

			//generate glyphs
			glyphs = bowlcut.text.split('').map(function(ch, chInd){
				var charElem = createSVGElement('text');
				charElem.textContent = ch;
				setAttributes(charElem, bowlcut.textAttributes);
				overwriteStyles(charElem, bowlcut.textStyles);
				glyphWidths[chInd] = Math.max(measureText(ch), bowlcut.textStyles['font-size']? Number(bowlcut.textStyles['font-size'].replace(/\D+/,''))/4:4.5);
				return charElem;
			});

			if(measureText(bowlcut.text) > bowlcut.pathLength){
				textBehaviorsToPlacements[bowlcut.maxBehavior]();
			}
			else {
				textBehaviorsToPlacements[bowlcut.minBehavior]();
			}

			return textGroup;
		},

		get: {
			pointOnPath: function(length){
				if(bowlcut.pathReverse) {
					return bowlcut.path.getPointAtLength(bowlcut.pathLength - length);
				}
				else {
					return bowlcut.path.getPointAtLength(length);
				}
			}
		},

		set: {
			path: function(element /*reverse*/){
				//save the path & any metrics we need
				bowlcut.path = element;
				bowlcut.pathReverse = arguments[1] || false;
				bowlcut.pathLength = element.getTotalLength();
				return bowlcut;
			},
			pathFromCircle: function(x, y, r, reverse, flipText){
				bowlcut.path = createCirclePath(x,y,r, flipText);
				bowlcut.pathReverse = reverse;
				bowlcut.pathLength = bowlcut.path.getTotalLength();
				return bowlcut;
			},
			pathFromArc: function(x, y, r, angle, upOrDown){
				var startAngle, endAngle,lengthFlag;
				if(upOrDown === 'up'){
					startAngle = -angle/2;
					endAngle = angle/2;
					bowlcut.path = createArc(x,y,r,startAngle, endAngle,false);
					bowlcut.pathReverse = false;
				}
				else {
					startAngle = 180-angle/2;
					endAngle = 180+angle/2;
					bowlcut.path = createArc(x,y,r,startAngle, endAngle,true);
					bowlcut.pathReverse = true;
				}
				
				bowlcut.pathLength = bowlcut.path.getTotalLength();
				return bowlcut;
			},
			text: function(str){
				bowlcut.text = str;
				bowlcut.textLength = measureText(str);
				return bowlcut;
			},
			styles: function(styleObj){
				for(var st in styleObj){
					bowlcut.textStyles[st] = styleObj[st];
				}
				return bowlcut;
			},
			attributes: function(attrObj){
				for(var st in attrObj){
					bowlcut.textAttributes[st] = attrObj[st];
				}
				return bowlcut;
			},
			padding: function(pad){
				bowlcut.padding = pad;
				return bowlcut;
			},
			minBehavior: function(mb){
				bowlcut.minBehavior = mb;
				return bowlcut;
			},
			maxBehavior: function(mb){
				bowlcut.maxBehavior = mb;
				return bowlcut;
			},
			glyphBehavior: function(gb){
				bowlcut.glyphBehavior = gb;
				return bowlcut;
			}
		}
	};

	return bowlcut;

	//helper methods

	function createSVGElement(elem){
		return document.createElementNS('http://www.w3.org/2000/svg', elem);
	}

	function setAttributes(elem, attrObj){
		for(var attr in attrObj){
			elem.setAttribute(attr, attrObj[attr]);
		}
	}

	function overwriteStyles(elem, styleObj){
		var styleString = '';
		for(var style in styleObj){
			styleString += style + ': ' + styleObj[style] + '; ';
		}
		elem.setAttribute('style', styleString);
	}

	function measureText(str){
		var tempSvg = createSVGElement('svg'),
			tempText = createSVGElement('text'),
			endsInWhitespace = false,
			length = 0;
		setAttributes(tempSvg, {
			width: 1,
			height: 1
		});
		overwriteStyles(tempSvg, {
			position: 'absolute',
			left: '-999px',
			top: '-999px'
		});

		if(str.match(/\s$/) !== null){
			//our string ends in whitespace that will be dropped
			endsInWhitespace = true;
			str+='.';
			var withPeriodLength = measureText(str),
				periodLength = measureText('.');
				return withPeriodLength - periodLength;
		}

		tempText.textContent = str;
		setAttributes(tempText, bowlcut.textAttributes);
		overwriteStyles(tempText, bowlcut.textStyles);
		document.body.appendChild(tempSvg);
		tempSvg.appendChild(tempText);
		length = tempText.getBBox().width;
		length += bowlcut.padding * str.length;
		document.body.removeChild(tempSvg);

		if(endsInWhitespace){

		}
		return length;
	}

	function dotProduct(a, b){
		return (a.x*b.x) + (a.y*b.y);
	}

	function normalize(a){
		var magnitude = Math.sqrt(Math.pow(a.x,2) + Math.pow(a.y,2));
		return {x: a.x/magnitude, y: a.y/magnitude};
	}

	//To be used for arc text generation
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

	function createArc(x,y,r,startAngle, endAngle, flipText){
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

	function sign(num){
		if (num === 0 || isNaN(num)){
			return num;
		}
		return num > 0 ? -1 : 1;
	}
};