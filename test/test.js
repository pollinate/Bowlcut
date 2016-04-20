/*global Bowlcut*/

'use strict';

var //centerSVG = //document.querySelector('#center-test'),
	//reverseSVG = document.querySelector('#reverse-test'),
	circleSVG = document.querySelector('#circle-test'),
	textInput = document.querySelector('input'),
	glyphBehaviorSelect = document.querySelector('#glyphbehavior-select'),
	minBehaviorSelect = document.querySelector('#minbehavior-select'),
	maxBehaviorSelect = document.querySelector('#maxbehavior-select'),
	//centerCut = new Bowlcut(),
	//reverseCut = new Bowlcut(),
	circleCut = new Bowlcut(),
	textPaths = [circleCut]; //centerCut, reverseCut, 

//centerCut.set.path(centerSVG.querySelector('path'), false);
//reverseCut.set.path(reverseSVG.querySelector('path'), true);
circleCut.set.pathFromArc(250,300,200,70,'up');
circleSVG.appendChild(circleCut.path);

textPaths.forEach(function(bc){
	bc.set.text(textInput.value)
	.set.styles({'font-size': '36px'})
	.set.attributes({'dy': '0'})
	.set.minBehavior(minBehaviorSelect.value)
	.set.maxBehavior(maxBehaviorSelect.value)
	.set.glyphBehavior(glyphBehaviorSelect.value);
});

redraw();

function redraw(){

	textPaths.forEach(function(bc){
		var previousRender= document.querySelector('#bowlcut-'+bc.uniqueId);
		if(previousRender){
			previousRender.parentNode.removeChild(previousRender);
		}
		bc.set.text(textInput.value)
		.set.minBehavior(minBehaviorSelect.value)
		.set.maxBehavior(maxBehaviorSelect.value)
		.set.glyphBehavior(glyphBehaviorSelect.value);
		var textToAppend = bc.render();
		/*if(bc.uniqueId === centerCut.uniqueId){
			centerSVG.appendChild(textToAppend);
		}
		else if(bc.uniqueId === reverseCut.uniqueId){
			reverseSVG.appendChild(textToAppend);
		}
		else if(bc.uniqueId === circleCut.uniqueId){*/
			circleSVG.appendChild(textToAppend);
		//}
	});
}
