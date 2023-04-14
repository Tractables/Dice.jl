present [![present on npm](https://img.shields.io/npm/dm/present.svg?maxAge=2592000)](https://www.npmjs.com/package/present) [![build status](https://img.shields.io/travis/dbkaplun/present.svg?maxAge=2592000)](https://travis-ci.org/dbkaplun/present)
=======

High-res timestamps in Node and browser

Installation
------------

In Node: `npm install present`

In browser:

1. Copy `present.js` or `present.min.js` (with optional source map at `present.min.js.map`)
2. `<script src="path/to/present.{min.}js"></script>`
3. `performance.now` is automatically polyfilled -- if this is undesired, `present.noConflict();`

Usage
-----
_Node only:_ `var present = require('present');`

### `present()`

Returns a timestamp in milliseconds. In node, this uses `process.hrtime`. In the browser, the following are attempted (in order):

* `performance.now()`
* `performance.webkitNow()`
* `performance.msNow()`
* `performance.mozNow()`
* `performance.oNow()`
* `Date.now()`
* `new Date().getTime()`

### `present.noConflict()`
_Browser only._ Resets `performance.now` to what it was before `present` was included or `present.conflict` was called.

### `present.conflict()`
_Browser only._ Polyfills `performance.now`.
