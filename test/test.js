(function(Bowlcut, opentype){
	'use strict';

	var centerSVG = document.querySelector('#center-test'),
		reverseSVG = document.querySelector('#reverse-test'),
		circleSVG = document.querySelector('#circle-test'),
		textInput = document.querySelector('input'),
		glyphBehaviorSelect = document.querySelector('#glyphbehavior-select'),
		minBehaviorSelect = document.querySelector('#minbehavior-select'),
		maxBehaviorSelect = document.querySelector('#maxbehavior-select'),
		centerCut = new Bowlcut.TextPath(),
		reverseCut = new Bowlcut.TextPath(),
		circleCut = new Bowlcut.TextPath(),
		textPaths = [circleCut, centerCut, reverseCut];

	centerCut.setPath(centerSVG.querySelector('path'), false);
	reverseCut.setPath(reverseSVG.querySelector('path'), true);
	circleCut.setPathFromArc(250,0,200,135,'down');
	circleSVG.appendChild(circleCut.path);

	opentype.load('expressway-regular.otf', function(err, font){
		if(err){
			console.error(err);
		}
		else{
			textPaths.forEach(function(tPath){
				tPath.font = font;
				tPath.attributes = {
					fill: 'red',
					fontSize: 36,
					stroke: 'green',
					strokeWidth: 3
				};
			});

			redraw();

			glyphBehaviorSelect.onchange = redraw;
			minBehaviorSelect.onchange = redraw;
			maxBehaviorSelect.onchange = redraw;
			textInput.oninput = redraw;
		}
	});

	function redraw(){

		textPaths.forEach(function(tPath){
			var previousRender= document.querySelector('#bowlcut-'+tPath.uniqueId);
			if(previousRender){
				previousRender.parentNode.removeChild(previousRender);
			}
			tPath.text = textInput.value;
			tPath.minBehavior = minBehaviorSelect.value;
			tPath.maxBehavior = maxBehaviorSelect.value;
			tPath.glyphBehavior = glyphBehaviorSelect.value;
			var pathsToAppend = tPath.render();
			if(tPath.uniqueId === centerCut.uniqueId){
				centerSVG.appendChild(pathsToAppend);
			}
			else if(tPath.uniqueId === reverseCut.uniqueId){
				reverseSVG.appendChild(pathsToAppend);
			}
			else if(tPath.uniqueId === circleCut.uniqueId){
				circleSVG.appendChild(pathsToAppend);
			}
		});
	}
})(window.Bowlcut, window.opentype);
