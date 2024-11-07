# webppl-timeit

This package provides a function `timeit` that takes a thunk and returns an object with its return value and its runtime in milliseconds. For example,

    timeit(function(){
      var x = 1;
      sleep(750);
      return x;
    })

returns

    { value: 1,
      runtimeInMilliseconds: 751 }

## Installation

To globally install `webppl-timeit`, run:

    mkdir -p ~/.webppl
    npm install --prefix ~/.webppl webppl-timeit

This may print warnings (`npm WARN ENOENT`...) which can be ignored.

To update to the latest version, run:

    npm update --prefix ~/.webppl webppl-timeit

## Usage

Once installed, you can make `timeit` available to `program.wppl` by running:

    webppl program.wppl --require webppl-timeit

## License

MIT