// ==UserScript==
// @name         ts-text-watcher
// @namespace    http://tampermonkey.net/
// @version      1.0
// @description  Clean, minimal TypeScript watcher with types and modular structure.
// @author       You
// @match        *://*/*
// @grant        none
// ==/UserScript==

(function () {
    'use strict';

    const stamp = () =>
        new Date().toLocaleString(undefined, { hour12: false });

    type WatcherConfig = {
        target?: HTMLElement;
        match: string[];
        onMatch: (matched: string) => void;
        once?: boolean;
    };

    const log = (...args: unknown[]) =>
        console.log(`[${new Date().toLocaleTimeString()}]`, ...args);

    const clickButton = (label: string): void => {
        const button = Array.from(document.querySelectorAll('button'))
            .find((b) => b.innerText.trim() === label);
        if (button) {
            console.log(`${stamp()} click ${label}`);
            button.click();
        }
    };

    const createWatcher = (config: WatcherConfig): MutationObserver => {
        const {
            target = document.body,
            match,
            onMatch,
            once = false,
        } = config;

        const triggered = new Set<string>();

        const check = () => {
            const text = target.innerText;
            for (const str of match) {
                if (text.includes(str)) {
                    if (once && triggered.has(str)) continue;

                    console.log(`${stamp()} match ${str}`);

                    triggered.add(str);
                    onMatch(str);
                }
            }
        };

        const observer = new MutationObserver(check);
        observer.observe(target, {
            childList: true,
            subtree: true,
            characterData: true,
        });

        check(); // initial check
        return observer;
    };

    const main = () => {
        console.log(`${stamp()} TRIGGER`);

        createWatcher({
            match: ['Some text of interest', 'Or Some other text'],
            onMatch: () => clickButton('CLICKME'),
        });

        createWatcher({
            match: ['Even more text'],
            onMatch: () => clickButton('CLICKOTHER'),
        });
    };

    main();

})();