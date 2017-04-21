(function($, opentype, Bowlcut, Promise){
	'use strict';

	var staging = document.querySelector('#staging3');

	var fonts = {};
	var fontnames = [
		'PassionOne-Bold'
	];

	Promise.all([loadFonts()]).then(function(){

		var wordmark = new Bowlcut();

		wordmark.text = ['BOWLCUT.JS'];
		wordmark.colors = ['#030303'];
		wordmark.fonts = [fonts['PassionOne-Bold']];
		wordmark.debug = false;

		var dataA = {
			bounds: {
				x: 0,
				y: 0,
				width: 326,
				height: 242
			},
			font: 0,
			fill: 0,
			stroke: null,
			slice: {
				0: []
			},
			topPath: document.querySelector('#hair-top'),
			bottomPath: document.querySelector('#hair-bottom')
		};

		var regionA = wordmark.addRegion(dataA);
		staging.appendChild(wordmark.render());
	});

	function loadFonts(){
		return new Promise(function(res){
			var fontPromises = [];
			fontnames.forEach(function(fn){
				fontPromises.push(new Promise(function(fpres){
					opentype.load('fonts/'+fn+'.ttf', function(err, font){
						if (err) throw err;
						fonts[fn] = font;
						fpres(font);
					});
				}));
			});

			Promise.all(fontPromises).then(res);
		});
	}

})(window.$, window.opentype, window.Bowlcut, window.Promise);
