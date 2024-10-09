var getLowResNow = function() {
  return new Date().getTime();
}

var getNow = (((typeof window !== 'undefined') && window.performance) ?
              function(){ return window.performance.now() } :
              getLowResNow);

var sleep = function(ms){
  var now = getNow();
  while (getNow() < now + ms) {
    /* do nothing */
  } 
}

module.exports = {
  now: getNow,
  sleep: sleep
}
