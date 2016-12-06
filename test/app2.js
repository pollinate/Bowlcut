(function($, opentype, Bowlcut){
	'use strict';

	var staging = document.querySelector('#staging2');

	var fonts = {};
	var fontnames = [
		'Collegiate',
		'UA_Full_Block'
	];

	Promise.all([loadFonts()]).then(function(){

		var wordmark = new Bowlcut();

		wordmark.text = ['example', 'wordmark'];
		wordmark.colors = ['#ff0000', '#00ccff'];
		wordmark.fonts = [fonts['Collegiate'], fonts['UA_Full_Block']];
		wordmark.debug = false;

		var dataA = {
			bounds: {
				x: 128,
				y: 128,
				width: 256,
				height: 64
			},
			font: 1,
			fill: 0,
			stroke: 1,
			slice: {
				0: []
			},
			topPath: null,
			bottomPath: null
		};

		var dataB = {
			bounds: {
				x: 128,
				y: 224,
				width: 256,
				height: 64
			},
			font: 0,
			fill: 1,
			stroke: null, 
			slice: {
				1: [4]
			},
			topPath: null,
			bottomPath: null
		};

		var regionA = wordmark.addRegion(dataA);
		var regionB = wordmark.addRegion(dataB);

		regionA.makeRadialArch(0.5);
		regionB.makeArch(0, 0.3);

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

})(window.$, window.opentype, window.Bowlcut);