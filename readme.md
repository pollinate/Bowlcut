![Alt](./examples/logo.svg "The project logo")

## A library for hairy SVG text manipulation
Bowlcut.js is a library designed to stretch vector text between sets of paths. Specifically, Bowlcut uses TTF fonts to produce styled SVG paths. Bowlcut wordmarks can have multiple region that text flows between, as many fonts as you would like, and a set of colors for various fills and strokes. Bowlcut was originally built for procedurally generating sports team logos, but it has many other applications as well in graphic design and inventive text layouts.

Bowlcut is designed to be used in a browser context, because some of its dependencies rely on isng the DOM for measuring the size of paths. The built file provided for use is an ES6 module, but it is provided as a bundle because its dependencies are commonjs modules that have to be included with it. You can edit the Rollup config file and run your own builds for additional contexts.

## Installation
Add this to your project's package.json file's dependencies:
```
	"Bowlcut.js": "ssh://git@github.com:pollinate/Bowlcut.js.git"
```
then
```
	npm i
```
Bowlcut is an ES6 module, so you will need to import it into your coes:
```
	import {Bowlcut} from 'node_modules/Bowlcut.js/dist/bundle.js';
```

## Use
A Bowlcut object is a renderable collection of styled text grouped into regions. These regions reference properties on the Bowlcut object for their styling, and have some properties of their own. Here's an example of how to set up a Bowlcut object.

```
	var wordmark = new Bowlcut({
		text: ['example', 'wordmark'],
		colors: ['#ff0000', '#00ccff']
	});

	/* other properties:
		precision (decimal places, defaults to 3)
		debug (true / false). Shows paths defining the regions
		uniqueId (hex string set up by the constructor)
	*/

	//now load the fonts (returns a promise):
	wordmark.loadFonts([
		['Modak-Regular', 'fonts/Modak-Regular.ttf'],
		['PassionOne-Bold', 'fonts/PassionOne-Bold.ttf']
	]);

```

Region objects define the position, styling, and bounding paths of text in the Bowlcut object. First properties are passed to the constructor, then the bounding paths are set.

```
	//some example region data
	var dataA = {
		bounds: {
			x: 128,
			y: 128,
			width: 256,
			height: 64
		},
		font: 1, // use the index of the font in the Bowlcut object
		fill: 0,
		stroke: 1,
		slice: {
			0: []	// key is the index of the string
					// value is an array of arguments for String.slice()
		},
		topPath: null,	// you can pass path elements here if you like
						// there are convenience methods detailed below for common shapes
		bottomPath: null,
		stretchToWidth: false, //default is false. Set to true to fill bounds when text width < bounds width
							  // otherwise text will be centered in the bounds
		advanceWidthScale: 1.0 // default is 1. this adjusts letter spacing before scaling and stretching is applied.
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
			1: [4] // will return 'mark'
		},
		topPath: null,
		bottomPath: null
	};

	var regionA = wordmark.addRegion(dataA);
	var regionB = wordmark.addRegion(dataB);
```

Here's what setting up the bounding paths looks like.

```
	regionA.makeRadialArch(0.5); //value of 0-1

	regionB.makeArch(0, 0.3);	// creates a bridge arch, with a flat top and a curved-up bottom
								// these values are on a scale of 0-1 with respect to the bounds height

	//also available: region.makeStraightPaths() for unwarped regions
```

Finally, to render:

```
	someSvg.appendChild(wordmark.render());

	//the render() function returns an SVG group of paths representing the regions.
```

And the final output:

![Alt](./examples/readme-output.svg "Example Bowlcut image")

This example is provided as working code under `examples/readme.html` in the repository.

## Samples
Start a local server in the main folder, and navigate to examples/methods.html, examples/logo.html, or examples/readme.html to see Bowlcut in action.

## Upcoming features and fixes
- Negative values for radial arch
- Further incorporation of Bezier.js LUT functionality and point sampling
- A set of unit tests for the path parsing functions

## License info
Bowlcut.js is distributed under the MIT License.

The example fonts included are from [Google Fonts](fonts.google.com) and are distributed under the [Open Font License](http://scripts.sil.org/cms/scripts/page.php?site_id=nrsi&id=OFL_web).
