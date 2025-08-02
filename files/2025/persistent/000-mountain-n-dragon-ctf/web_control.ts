import * as g from "./globals.ts";
import * as reconstructed_tape from "./autogen/reconstructed_tape.ts";

export var m_connected: boolean = false;
export var m_opt_socket: WebSocket | undefined = undefined;
export var m_opt_data_socket: WebSocket | undefined = undefined;

export var m_tape_snapshot: number[] = [...g.g.tape];

export var m_do_reset = false;
export var m_do_diff_tape = false;
export var m_do_diff_last_tape = false;
export var m_do_verify_tape = false;

export var m_do_read = false;
export var m_do_write = false;
export var m_addr16_to_access_or_nan = NaN;
export var m_val_to_write_or_nan = NaN;

export var m_watching_addresses: number[] = [];

export function connect(
  server: string,
  port: number,
  on_message: (event: MessageEvent<any>) => void
): WebSocket {
  // Create WebSocket connection.
  const socket = new WebSocket(`ws://${server}:${port}`);

  socket.addEventListener("open", (_event) => {
    console.log("web_control: open");
    m_connected = true;
  });

  socket.addEventListener("close", (_event) => {
    console.log("web_control: close");
    m_connected = false;
  });

  socket.addEventListener("error", (event) => {
    console.log(`web_control encountered an error: ${event}`);
  });

  socket.addEventListener("message", (event) => {
    // console.log("Message from server ", event.data);
    on_message(event);
  });

  return socket;
}

export function stamp(): string {
  return new Date().toLocaleString(undefined, { hour12: false });
}

export function log_info(s: string) {
  console.log(`${stamp()} - INFO - ${s}`);
}

export function web_error(msg: string) {
  if (!m_opt_socket) throw new Error("socket is not defined");

  m_opt_socket.send(`${stamp()} - Error - ${msg}`);

  throw new Error(msg);
}

export function web_warn(msg: string) {
  if (!m_opt_socket) throw new Error("socket is not defined");

  m_opt_socket.send(`${stamp()} - Warn - ${msg}`);
}

export function web_info(msg: string) {
  if (!m_opt_socket) throw new Error("socket is not defined");

  m_opt_socket.send(`${stamp()} - Info - ${msg}`);
}

export function web_debug(msg: string) {
  if (!m_opt_socket) throw new Error("socket is not defined");

  m_opt_socket.send(`${stamp()} - Debug - ${msg}`);
}

export function web_trace(msg: string) {
  if (!m_opt_data_socket) {
    web_error("data socket is not connected. Please use /data-connect.");
    return; // unreachable
  }

  m_opt_data_socket.send(`${stamp()} - Trace - ${msg}`);
}

export function web_send(msg: string) {
  if (!m_opt_socket) throw new Error("socket is not defined");

  m_opt_socket.send(`${msg}`);
}

export function verify_tape_integrity() {
  const expected_simple_checksum = 287251;
  const expected_num_elements = 13229;

  if (g.g.tape.length != expected_num_elements) {
    const err = `Expected tape length ${expected_num_elements} but got ${g.g.tape.length}`;

    if (m_opt_socket) {
      web_warn(err);
    } else {
      throw new Error(err);
    }
  }

  var sum = 0;

  for (var i = 0; i < g.g.tape.length; i++) {
    sum += g.g.tape[i];
  }

  if (sum != expected_simple_checksum) {
    const err = `Expected tape sum ${expected_simple_checksum} but got ${sum}`;
    if (m_opt_socket) {
      web_warn(err);
      return;
    } else {
      throw new Error(err);
    }
  }

  console.log("tape OK");

  if (m_opt_socket) {
    m_opt_socket.send("tape OK");
  }
}

export function addr16(n: number): string {
  return `0x${n.toString(16).padStart(4, "0")}`;
}

export function display_array_diff(
  arr1: number[],
  arr2: number[],
  name1: string,
  name2: string
) {
  web_send(`${name1}.length: ${arr1.length}, ${name2}.length: ${arr2.length}`);

  var shared_data_length =
    arr1.length < arr2.length ? arr1.length : arr2.length;

  for (var i = 0; i < shared_data_length; i++) {
    if (arr1[i] != arr2[i]) {
      web_send(`${addr16(i)}: ${arr1[i]} != ${arr2[i]}`);
    }
  }

  if (arr1.length > arr2.length) {
    for (var i = shared_data_length; i < arr1.length; i++) {
      if (arr1[i] != arr2[i]) {
        web_send(`${addr16(i)}: ${arr1[i]} != NA`);
      }
    }
  } else {
    for (var i = shared_data_length; i < arr2.length; i++) {
      web_send(`${addr16(i)}: NA != ${arr2[i]}`);
    }
  }
}

export function on_interval() {
  for (var i = 0; i < m_watching_addresses.length; i++) {
    const cur_addr16 = m_watching_addresses[i];

    const opt_value = g.g.tape[cur_addr16];

    if (opt_value == undefined) {
      web_trace(`${addr16(cur_addr16)}: cannot read`);
    } else {
      web_trace(`${addr16(cur_addr16)}: ${opt_value}`);
    }
  }
}

export function on_update() {
  if (m_do_reset) {
    g.g.inp = 0;
    g.g.cond_reg = false;
    (g.g.reg16 = 0),
      (g.g.pc16 = 0),
      (g.g.sp16 = 0),
      (g.g.inst8 = 0),
      (g.g.new_frame = 0);

    g.g.joyp[37] = 0;
    g.g.joyp[38] = 0;
    g.g.joyp[39] = 0;
    g.g.joyp[40] = 0;
    g.g.joyp[88] = 0;
    g.g.joyp[90] = 0;

    g.g.tape = reconstructed_tape.reconstruct_tape();

    m_do_reset = false;
  }

  if (m_do_diff_tape) {
    var orig_tape = reconstructed_tape.reconstruct_tape();
    display_array_diff(orig_tape, g.g.tape, "orig", "tape");
    m_tape_snapshot = [...g.g.tape];

    m_do_diff_tape = false;
  }

  if (m_do_diff_last_tape) {
    display_array_diff(m_tape_snapshot, g.g.tape, "snap", "tape");
    m_tape_snapshot = [...g.g.tape];

    m_do_diff_last_tape = false;
  }

  if (m_do_verify_tape) {
    verify_tape_integrity();

    m_do_verify_tape = false;
  }

  if (m_do_read) {
    if (Number.isNaN(m_addr16_to_access_or_nan)) {
      web_warn("addr16 is NaN");
    } else {
      const opt_value = g.g.tape[m_addr16_to_access_or_nan];
      if (opt_value == undefined) {
        web_warn(
          `Could not read value at ${addr16(m_addr16_to_access_or_nan)}`
        );
      } else {
        web_send(`Reading ${addr16(m_addr16_to_access_or_nan)}`);
        web_send(opt_value.toString());
      }
    }

    m_addr16_to_access_or_nan = NaN;
    m_do_read = false;
  }

  if (m_do_write) {
    if (Number.isNaN(m_addr16_to_access_or_nan)) {
      web_warn("addr16 is NaN");
    } else if (Number.isNaN(m_val_to_write_or_nan)) {
      web_warn("val is NaN");
    } else {
      web_send(
        `Writing ${m_val_to_write_or_nan} to ${addr16(
          m_addr16_to_access_or_nan
        )}`
      );
      g.g.tape[m_addr16_to_access_or_nan] = m_val_to_write_or_nan;
    }

    m_val_to_write_or_nan = NaN;
    m_addr16_to_access_or_nan = NaN;
    m_do_write = false;
  }
}

export function start() {
  setInterval(on_interval, 1000);

  m_opt_socket = connect("localhost", 3004, (event) => {
    if (!m_opt_socket) throw new Error("socket is not defined");

    const message: string = event.data;

    if (message.startsWith("/hello")) {
      m_opt_socket.send("Hello hello!");
    } else if (message.startsWith("/help")) {
      m_opt_socket.send("Possible commands are");
      m_opt_socket.send("/hello                 - Sends a hello");
      m_opt_socket.send("/help                  - Displays this message");
      m_opt_socket.send(
        "/reset                 - Restart your adventure! No refreshing needed!"
      );
      m_opt_socket.send(
        "/diff-tape             - Shows changes on the tape from the original"
      );
      m_opt_socket.send(
        "/diff-last-tape        - Shows changes on the tape since the last snapshot"
      );
      m_opt_socket.send(
        "/verify-tape           - Runs integrity test on the tape"
      );
      m_opt_socket.send(
        "/read {addr16}         - Reads the value in the specified position"
      );
      m_opt_socket.send(
        "/write {addr16} {val}  - Writes a value to the specified position"
      );
      m_opt_socket.send(
        "/watch {addr16}        - Reads the value at the address every second"
      );
      m_opt_socket.send(
        "/nowatch {addr16}      - Stops reading the value at the address every second"
      );
      m_opt_socket.send(
        "/data-connect          - Connect to a side channel websocket server for data transmissions"
      );
    } else if (message.startsWith("/reset")) {
      m_opt_socket.send("Resetting");
      m_do_reset = true;
    } else if (message.startsWith("/diff-tape")) {
      m_do_diff_tape = true;
    } else if (message.startsWith("/diff-last-tape")) {
      m_do_diff_last_tape = true;
    } else if (message.startsWith("/verify-tape")) {
      m_do_verify_tape = true;
    } else if (message.startsWith("/read")) {
      const tokens = message.split(" ");

      if (tokens.length != 2) {
        web_warn(`Usage: /read {addr16}`);
      } else {
        m_do_read = true;
        m_addr16_to_access_or_nan = Number(tokens[1]);
      }
    } else if (message.startsWith("/write")) {
      const tokens = message.split(" ");

      if (tokens.length != 3) {
        web_warn(`Usage: /write {addr16} {val}`);
      } else {
        m_do_write = true;
        m_addr16_to_access_or_nan = Number(tokens[1]);
        m_val_to_write_or_nan = Number(tokens[2]);
      }
    } else if (message.startsWith("/watch")) {
      const tokens = message.split(" ");

      if (tokens.length != 2) {
        web_warn(`Usage: /watch {addr16}`);
      } else {
        m_do_write = true;
        const addr16_or_nan = Number(tokens[1]);

        if (Number.isNaN(addr16_or_nan)) {
          web_warn("address provided is invalid");
        } else {
          if (!m_watching_addresses.includes(addr16_or_nan)) {
            m_watching_addresses.push(addr16_or_nan);
          }
        }
      }
    } else if (message.startsWith("/nowatch")) {
      const tokens = message.split(" ");

      if (tokens.length != 2) {
        web_warn(`Usage: /nowatch {addr16}`);
      } else {
        m_do_write = true;
        const addr16_or_nan = Number(tokens[1]);

        if (Number.isNaN(addr16_or_nan)) {
          web_warn("address provided is invalid");
        } else {
          web_info(`Removing address ${addr16(addr16_or_nan)}`);
          m_watching_addresses = m_watching_addresses.filter(
            (item) => item !== addr16_or_nan
          );
        }
      }
    } else if (message.startsWith("/data-connect")) {
      web_info("Connecting to data channel");
      m_opt_data_socket = connect("localhost", 3005, (_event) => {});
      setTimeout(() => {
        web_trace(`Connected to data channel`);
        }, 500);
    }
  });
}
