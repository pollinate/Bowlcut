![Alt](./examples/logo.svg "The project logo")

## A library for hairy SVG text manipulation

## Installation
Add this to your project's package.json file's dependencies:
```
	"Bowlcut.js": "ssh://git@bitbucket.org:pollinate-dev/bowlcut.js.git"
```
then
```
	npm i
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
- Debug mode is largely incompatible withe the papercut  operation.

## License info
Bowlcut.js is distributed under the MIT License.

The example fonts included are from [Google Fonts](fonts.google.com) and are distributed under the [Open Font License](http://scripts.sil.org/cms/scripts/page.php?site_id=nrsi&id=OFL_web).
