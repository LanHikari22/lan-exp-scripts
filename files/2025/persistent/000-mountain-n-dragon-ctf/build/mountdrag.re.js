(() => {
  // mountdrag.re.ts
  var joyp = {};
  joyp[37] = 0;
  joyp[38] = 0;
  joyp[39] = 0;
  joyp[40] = 0;
  joyp[88] = 0;
  joyp[90] = 0;
  window.onkeyup = function(e) {
    joyp[e.keyCode] = 0;
  };
  window.onkeydown = function(e) {
    joyp[e.keyCode] = 1;
  };
  var mq = document.getElementById("marquee");
})();
