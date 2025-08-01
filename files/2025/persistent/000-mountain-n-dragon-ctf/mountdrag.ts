//null
//original(?) by thisismypassword
//ported to javascript by 2Tie for OLJ '19
//Deluxe edition by 2Tie for REJ '24

import * as webio from "./webio.ts";
import * as reconstructed_tape from './autogen/reconstructed_tape.ts'


export var g_tape = reconstructed_tape.reconstruct_tape();

function verify_tape_integrity() {
  const expected_simple_checksum = 287251;
  const expected_num_elements = 13229;

  if (g_tape.length != expected_num_elements) {
    throw new Error(`Expected tape length ${expected_num_elements} but got ${g_tape.length}`);
  }

  var sum = 0;
  
  for (var i=0; i<g_tape.length; i++) {
    sum += g_tape[i];
  }

  if (sum != expected_simple_checksum) {
    throw new Error(`Expected tape sum ${expected_simple_checksum} but got ${sum}`);
  }

  console.log("tape OK");
}

export var g_cmds = [
  // 0
  function () {
    g_reg16 = get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 1
  function () {
    // Write register data to the next u16 inst
    g_tape[get_and_adv_tape_u16()] = g_reg16;
  },

  // 2
  function () {
    g_tape[get_and_adv_tape_u16()] = g_tape[g_reg16];
  },

  // 3
  function () {
    g_tape[g_reg16] = get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 4
  function () {
    g_reg16 += get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 5
  function () {
    g_reg16 -= get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 6
  function () {
    g_cond_reg = g_reg16 == get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 7
  function () {
    g_cond_reg = g_reg16 < get_and_adv_tape_u16_and_load_on_odd_caller();
  },
  // 8
  function () {
    g_cond_reg = 0 != (g_reg16 & get_and_adv_tape_u16_and_load_on_odd_caller());
  },

  // 9
  function () {
    g_reg16 = g_reg16 & get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 10
  function () {
    g_reg16 = g_reg16 | get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 11
  function () {
    g_reg16 = g_reg16 ^ get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 12
  function () {
    g_pc16 = get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 13
  function () {
    var v = get_and_adv_tape_u16_and_load_on_odd_caller();
    g_pc16 = g_cond_reg ? v : g_pc16;
  },

  // 14
  function () {
    var v = get_and_adv_tape_u16_and_load_on_odd_caller();
    g_pc16 = g_cond_reg ? g_pc16 : v;
  },

  // 15
  function () {
    g_sp16 -= 1;
    g_tape[g_sp16] = g_pc16 + 2;
    g_pc16 = get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 16
  function () {
    g_pc16 = g_tape[g_sp16];
    g_sp16 += 1;
  },

  // 17
  function () {
    g_sp16 -= 1;
    g_tape[g_sp16] = g_reg16;
  },

  // 18
  function () {
    g_reg16 = g_tape[g_sp16];
    g_sp16 += 1;
  },

  // 19
  function () {
    g_exit_code = 1;
  },

  // 20
  function () {
    g_inp = 0;
    g_inp +=
      g_joyp[37] +
      (g_joyp[39] << 1) +
      (g_joyp[38] << 2) +
      (g_joyp[40] << 3) +
      (g_joyp[90] << 4) +
      (g_joyp[88] << 5);
    g_reg16 = g_inp;
  },

  // 21
  function () {
    // Function`$${"\x61 \x3D\x20\x6E\x65\x77 \x44\x61\x74\x65\x28\x29\x5B\x27\x67\x65\x74\x53\x65\x63\x6F\x6E\x64\x73\x27\x5D\x28\x29 "}$`();
    // Hex for:
    // a = new Date()['getSeconds']()

    g_reg16 = new Date()['getSeconds']()
  },

  // 22
  function () {
    this.document.location.href = "" + l(g_reg16) + ".html";
  },
];

function get_and_adv_tape() {
  var v = g_tape[g_pc16];
  g_pc16 += 1;
  return v;
}

function get_and_adv_tape_u16() {
  var v = get_and_adv_tape();
  return v + (get_and_adv_tape() << 8);
}

function get_and_adv_tape_u16_and_load_on_odd_caller() {
  var inst16 = get_and_adv_tape_u16();
  if (g_inst8 % 2 > 0) inst16 = g_tape[inst16] || 0;
  return inst16;
}

function l(v) {
  function y(v) {
    return "wnesai0123456789X".substring(v, v + 1);
  }

  var y1 = "";

  while (g_tape[v] != 255) {
    y1 = y1 + y(g_tape[v]);
    v += 1;
  }

  v += 1;

  var y2 = "";

  while (g_tape[v] != 255) {
    y2 = y2 + y(g_tape[v]);
    v += 1;
  }

  return y1 + y2;
}

var g_joyp = {};
g_joyp[37] = 0;
g_joyp[38] = 0;
g_joyp[39] = 0;
g_joyp[40] = 0;
g_joyp[88] = 0;
g_joyp[90] = 0;

window.onkeyup = function (e: KeyboardEvent) {
  g_joyp[e.keyCode] = 0;
};

window.onkeydown = function (e: KeyboardEvent) {
  g_joyp[e.keyCode] = 1;
};

var g_inp = 0;
var g_mq = document.getElementById("marquee");

var g_cond_reg = false;

var g_reg16 = 0,
  g_pc16 = 0,
  g_sp16 = 0,
  g_inst8 = 0,
  g_exit_code = 0;

// var g_socket = webio.connect("localhost", 3003, (event) => {
//   console.log(`Server: ${event.data}`)
// })

verify_tape_integrity()

// Starts out onload in html
export function mainloop() {
  g_exit_code = 0;
  g_inp = 0;

  var i = 0;

  while (g_exit_code == 0) {
    g_inst8 = get_and_adv_tape();

    var cmd_idx = Math.floor(g_inst8 / 2);

    // if (webio.m_connected) {
    //   g_socket.send(`${i++},${cmd_idx},${g_data_cur},${g_inst8}`)
    // }

    var fn = g_cmds[cmd_idx];
    if (fn) {
      fn();
    } 
  }

  if (!g_mq) {
    throw new TypeError('Error message');
  }

  // update black box with the input currently selected if any
  g_mq.innerHTML = " ";
  g_mq.innerHTML += ((g_inp >> 0) & 1) != 0 ? "L" : " ";
  g_mq.innerHTML += ((g_inp >> 1) & 1) != 0 ? "R" : " ";
  g_mq.innerHTML += ((g_inp >> 2) & 1) != 0 ? "F" : " ";
  g_mq.innerHTML += ((g_inp >> 3) & 1) != 0 ? "B" : " ";
  g_mq.innerHTML += ((g_inp >> 4) & 1) != 0 ? "I" : " ";
  g_mq.innerHTML += ((g_inp >> 5) & 1) != 0 ? "U" : " ";
  g_mq.innerHTML += " ";

  requestAnimationFrame(mainloop);
}
