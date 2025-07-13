// ==UserScript==
// @name         Packet Beeper
// @namespace    https://example.com/
// @version      1.0
// @description  TRIGGER on load; log "beep <timestamp> <type> <url>" for each fetch/XHR.
// @author       Lan
// @match        *://*/*
// @run-at       document-start
// @grant        none
// ==/UserScript==

console.log('TRIGGER');   // once per page load

(function () {
  'use strict';

  // helper: ISO-like timestamp in local time zone
  const stamp = () =>
    new Date().toLocaleString(undefined, { hour12: false });

  const observer = new PerformanceObserver(list => {
    list.getEntries().forEach(e => {
      if (e.initiatorType === 'fetch' || e.initiatorType === 'xmlhttprequest') {
        console.log(`${stamp()} beep ${e.initiatorType} ${e.name}`);
      }
    });
  });

  observer.observe({ type: 'resource', buffered: true });
})();
