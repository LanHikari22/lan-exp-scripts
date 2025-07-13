// ==UserScript==
// @name         text-match-click
// @namespace    http://tampermonkey.net/
// @version      1.0
// @description  Searches for text on the DOM. Clicks a specific button text on match.
// @author       Lan
// @match        *://*/*
// @grant        none
// ==/UserScript==

(function () {
    'use strict';
  
    const stamp = () =>
    	new Date().toLocaleString(undefined, { hour12: false });

  
    console.log(`${stamp()} TRIGGER`);


    const targetText = "Example text to always look for";
    const buttonLabel = "CLICKME";

    const observer = new MutationObserver(() => {
        if (document.body.innerText.includes(targetText)) {
            console.log(`${stamp()} match`);

            const buttons = Array.from(document.querySelectorAll("button"));
          
            const targetButton = buttons.find(btn => btn.innerText.trim() === buttonLabel);
          
            if (targetButton) {
                console.log(`${stamp()} click`);
                targetButton.click();
            }
        }
    });

    observer.observe(document.body, {
        childList: true,
        subtree: true,
        characterData: true
    });

})();
