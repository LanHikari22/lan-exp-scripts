import * as g from "./globals.ts";
import * as reconstructed_tape from './autogen/reconstructed_tape.ts'

export var m_connected: boolean = false;
export var m_opt_socket: WebSocket | undefined = undefined;  


export var m_tape_snapshot: number[] = [...g.g.tape];

export var m_do_reset = false;
export var m_do_diff_tape = false;
export var m_do_diff_last_tape = false;
export var m_do_verify_tape = false;


export function connect(server: string, port: number, on_message: (event: MessageEvent<any>) => void): WebSocket {
  // Create WebSocket connection.
  const socket = new WebSocket(`ws://${server}:${port}`);

  socket.addEventListener("open", (_event) => {
    console.log("web_control: open")
    m_connected = true;
  });

  socket.addEventListener("close", (_event) => {
    console.log("web_control: close")
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

export function web_error(msg: string) {
  if (!m_opt_socket) throw new Error("socket is not defined");

  m_opt_socket.send(`Error: ${msg}`)

  throw new Error(msg);
}

export function web_warn(msg: string) {
  if (!m_opt_socket) throw new Error("socket is not defined");

  m_opt_socket.send(`Warn: ${msg}`)
}

export function web_send(msg: string) {
  if (!m_opt_socket) throw new Error("socket is not defined");

  m_opt_socket.send(`${msg}`)
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
  
  for (var i=0; i<g.g.tape.length; i++) {
    sum += g.g.tape[i];
  }

  if (sum != expected_simple_checksum) {
    const err = `Expected tape sum ${expected_simple_checksum} but got ${sum}`;
    if (m_opt_socket) {
      web_warn(err);
      return;
    } else {
      throw new Error(err)
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

export function display_array_diff(arr1: number[], arr2: number[], name1: string, name2: string) {
    web_send(`${name1}.length: ${arr1.length}, ${name2}.length: ${arr2.length}`);

    var shared_data_length = arr1.length < arr2.length ? arr1.length : arr2.length;

    for (var i=0; i<shared_data_length; i++) {
        if (arr1[i] != arr2[i]) {
            web_send(`${addr16(i)}: ${arr1[i]} != ${arr2[i]}`)
        }
    }

    if (arr1.length > arr2.length) {
      for (var i=shared_data_length; i<arr1.length; i++) {
          if (arr1[i] != arr2[i]) {
              web_send(`${addr16(i)}: ${arr1[i]} != NA`)
          }
      }
    } else {
      for (var i=shared_data_length; i<arr2.length; i++) {
        web_send(`${addr16(i)}: NA != ${arr2[i]}`)
      }
    }
}

export function on_update() {
  if (m_do_reset) {
    g.g.inp = 0;
    g.g.cond_reg = false;
    g.g.reg16 = 0,
    g.g.pc16 = 0,
    g.g.sp16 = 0,
    g.g.inst8 = 0,
    g.g.new_frame = 0;

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
    display_array_diff(orig_tape, g.g.tape, 'orig', 'tape');
    m_tape_snapshot = [...g.g.tape];

    m_do_diff_tape = false;
  }

  if (m_do_diff_last_tape) {
    display_array_diff(m_tape_snapshot, g.g.tape, 'snap', 'tape');
    m_tape_snapshot = [...g.g.tape];

    m_do_diff_last_tape = false;
  }

  if (m_do_verify_tape) {
    verify_tape_integrity();

    m_do_verify_tape = false;
  }
}

export function start() {
    m_opt_socket = connect("localhost", 3004, (event) => {
        if (!m_opt_socket) throw new Error("socket is not defined");

        const message: string = event.data;

        if (message.startsWith("/hello")) {
            m_opt_socket.send("Hello hello!");
        }
        else if (message.startsWith("/help")) {
            m_opt_socket.send("Possible commands are");
            m_opt_socket.send("/hello            - Sends a hello");
            m_opt_socket.send("/help             - Displays this message");
            m_opt_socket.send("/reset            - Restart your adventure! No refreshing needed!");
            m_opt_socket.send("/diff-tape        - Shows changes on the tape from the original");
            m_opt_socket.send("/diff-last-tape   - Shows changes on the tape since the last snapshot");
            m_opt_socket.send("/verify-tape      - Runs integrity test on the tape");
        }
        else if (message.startsWith("/reset")) {
            m_opt_socket.send("Resetting");
            m_do_reset = true;
        }
        else if (message.startsWith("/diff-tape")) {
            m_do_diff_tape = true;
        }
        else if (message.startsWith("/diff-last-tape")) {
            m_do_diff_last_tape = true;
        }
        else if (message.startsWith("/verify-tape")) {
            m_do_verify_tape = true;
        }
    })
}