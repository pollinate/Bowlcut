<!-- Generated by documentation.js. Update this documentation by updating the source code. -->

### Table of Contents

-   [addRegion][1]
-   [fitTextInBounds][2]
-   [renderRegion][3]
-   [makeStraightPaths][4]
-   [makeArch][5]
-   [makeRadialArch][6]
-   [render][7]
-   [loadFonts][8]
-   [papercut][9]

## addRegion

addRegion creates and adds a region to a Bowlcut object

**Parameters**

-   `regionOptions` **[Object][10]** allow for overrides for fill, stroke, etc. to be passed in on construction of a region.

Returns **[Object][10]** the region object

## fitTextInBounds

fitTextInBounds scales the region's text to fit inside the region's bounds, with no other transformations

Returns **[Object][10]** the scaled text as an opentype Path

## renderRegion

renderRegion uses the provided bounds and top/bottom paths for a region to render an SVG path in between

Returns **[Object][10]** the rendered SVGPathElement

## makeStraightPaths

makeStraightPaths makes top and bottom paths from the verical edges of the region bounds

## makeArch

makeArch makes quadratic arcs for the top and bottom path of a region

**Parameters**

-   `topBend` **[Number][11]** can be positive or negative
-   `bottomBend` **[Number][11]** can be positive or negative

## makeRadialArch

makeRadialArch sets the region's paths to a rainbow-shaped arch from the bounds and a bend strength

**Parameters**

-   `radialBend` **[Number][11]** must be >= 0

## render

render creates an SVGGroupElement containing the rendered region paths

**Parameters**

-   `unify` **[Boolean][12]?** merges region paths with a union operation, removing overlaps. Expensive so defaults to false. (optional, default `false`)

Returns **[Object][10]** the group element

## loadFonts

loadFonts takes an array of tuples like so: \[[fontName, fontUrl], ...]]

**Parameters**

-   `fontTuples` **[Array][13]** 

Returns **[Object][10]** a promise resolved when the fonts have loaded

## papercut

papercut generates the union of each group of characters in an svg DOM element

**Parameters**

-   `domElem` **[Object][10]** svg element generated from Bowlcut.

Returns **[Object][10]** New svg DOM element with unions applied.

[1]: #addregion

[2]: #fittextinbounds

[3]: #renderregion

[4]: #makestraightpaths

[5]: #makearch

[6]: #makeradialarch

[7]: #render

[8]: #loadfonts

[9]: #papercut

[10]: https://developer.mozilla.org/docs/Web/JavaScript/Reference/Global_Objects/Object

[11]: https://developer.mozilla.org/docs/Web/JavaScript/Reference/Global_Objects/Number

[12]: https://developer.mozilla.org/docs/Web/JavaScript/Reference/Global_Objects/Boolean

[13]: https://developer.mozilla.org/docs/Web/JavaScript/Reference/Global_Objects/Array