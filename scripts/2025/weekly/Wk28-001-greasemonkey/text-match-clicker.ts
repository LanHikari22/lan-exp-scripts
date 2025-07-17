// ==UserScript==
// @name         ts-text-watcher
// @namespace    http://tampermonkey.net/
// @version      1.0
// @description  Clean, minimal TypeScript watcher with types and modular structure.
// @author       You
// @match        *://*/*
// @grant        none
// ==/UserScript==

import * as comm from "../persistent/000-greasemonkey/common";

(function () {
  "use strict";

  comm.hello();

  const main = () => {
    comm.log_info(`TRIGGER`);

    comm.watch_on_dom_text_change(
      ["Some text of interest", "Or Some other text"],
      () => comm.click_button("CLICKME")
    );

    comm.watch_on_dom_text_change(["Even more text"], () =>
      comm.click_button("CLICKOTHER")
    );
  };

  main();
})();
