// ==UserScript==
// @name         ts-text-watcher
// @namespace    http://tampermonkey.net/
// @version      1.0
// @description  Clean, minimal TypeScript watcher with types and modular structure.
// @author       You
// @match        *://*/*
// @grant        none
// ==/UserScript==

(() => {
  // text-match-clicker.ts
  (function() {
    "use strict";
    const stamp = () => (/* @__PURE__ */ new Date()).toLocaleString(void 0, { hour12: false });
    const log = (...args) => console.log(`[${(/* @__PURE__ */ new Date()).toLocaleTimeString()}]`, ...args);
    const clickButton = (label) => {
      const button = Array.from(document.querySelectorAll("button")).find((b) => b.innerText.trim() === label);
      if (button) {
        console.log(`${stamp()} click ${label}`);
        button.click();
      }
    };
    const createWatcher = (config) => {
      const {
        target = document.body,
        match,
        onMatch,
        once = false
      } = config;
      const triggered = /* @__PURE__ */ new Set();
      const check = () => {
        const text = target.innerText;
        for (const str of match) {
          if (text.includes(str)) {
            if (once && triggered.has(str)) continue;
            console.log(`${stamp()} match`);
            triggered.add(str);
            onMatch(str);
          }
        }
      };
      const observer = new MutationObserver(check);
      observer.observe(target, {
        childList: true,
        subtree: true,
        characterData: true
      });
      check();
      return observer;
    };
    const main = () => {
      console.log(`${stamp()} TRIGGER`);
      createWatcher({
        match: ["Some text of interest", "Or Some other text"],
        onMatch: () => clickButton("CLICKME")
      });
      createWatcher({
        match: ["Even more text"],
        onMatch: () => clickButton("CLICKOTHER")
      });
    };
    main();
  })();
})();
