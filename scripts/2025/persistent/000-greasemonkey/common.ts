// ------------------------------------------------------------------------------------------------
// \begin{misc}
export const DEFAULT_VERBOSE = true;

export function hello() {
  console.log("Hello World");
}

export function stamp(): string {
  return new Date().toLocaleString(undefined, { hour12: false });
}

export function log_info(s: string) {
  console.log(`${stamp()} - INFO - ${s}`);
}

export function notImplemented(): never {
  throw new Error("not Implemented");
}
// \end{misc}
// ------------------------------------------------------------------------------------------------

// ------------------------------------------------------------------------------------------------
// \begin{webactions}

export function click_button(
  label: string,
  verbose: boolean = DEFAULT_VERBOSE
): void {
  const button = Array.from(document.querySelectorAll("button")).find(
    (b) => b.innerText.trim() === label
  );

  if (button) {
    if (verbose) {
      log_info(`click ${label}`);
    }
    button.click();
  }
}

export function read_node_with_xpath(xpath: string): Node | undefined {
  var result = document.evaluate(
    xpath,
    document,
    null,
    XPathResult.FIRST_ORDERED_NODE_TYPE,
    null
  );

  if (!result.singleNodeValue) {
    return undefined;
  }

  return result.singleNodeValue;
}

export function read_html_elem_with_xpath(
  xpath: string
): HTMLElement | undefined {
  return read_node_with_xpath(xpath) as HTMLElement;
}

export function read_html_input_with_xpath(
  xpath: string
): HTMLInputElement | undefined {
  return read_node_with_xpath(xpath) as HTMLInputElement;
}

/**
 * matches may start with ^ for startsWith check,
 * or end with $ for endsWith check.
 * Otherwise it's an includes check.
 */
export function check_string_start_end_incl(
  to_check: string,
  s: string
): boolean {
  return (
    to_check.includes(s) ||
    (s.endsWith("$") && to_check.endsWith(s.slice(0, s.length - 1))) ||
    (s.startsWith("^") && to_check.startsWith(s.slice(1, s.length)))
  );
}

export function watch_on_dom_text_change(
  matches: string[],
  on_match: (matched: string) => void,
  once: boolean = false,
  verbose: boolean = DEFAULT_VERBOSE
) {
  const target = document.body;

  const triggered = new Set<string>();

  const check = () => {
    const text = target.innerText;
    for (const s of matches) {
      if (check_string_start_end_incl(text, s)) {
        if (once && triggered.has(s)) continue;

        if (verbose) {
          log_info(`match ${s}`);
        }

        triggered.add(s);
        on_match(s);
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
}

export function watch_on_network_packet(
  matches: string[],
  on_match: () => void,
  verbose: boolean = DEFAULT_VERBOSE
) {
  const observer = new PerformanceObserver((list) => {
    list //_
      .getEntries()
      .forEach((e) => {
        // log_info(`${JSON.stringify(e)}`);
        const e1 = e as PerformanceResourceTiming;

        if (
          e1.initiatorType === "fetch" ||
          e1.initiatorType === "xmlhttprequest"
        ) {
          if (matches.length == 0) {
            if (verbose) {
              log_info(`beep ${e1.initiatorType} ${e.name}`);
            }
          }

          for (const s of matches) {
            if (check_string_start_end_incl(e.name, s)) {
              if (verbose) {
                log_info(`network match ${e1.initiatorType} ${e.name}`);
              }

              on_match();
            }
          }
        }
      });
  });

  observer.observe({ type: "resource", buffered: true });
}

// \end{webactions}
// ------------------------------------------------------------------------------------------------

// ------------------------------------------------------------------------------------------------
// \begin{tmpl}
// \end{tmpl}
// ------------------------------------------------------------------------------------------------
