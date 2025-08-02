//null
//original(?) by thisismypassword
//ported to javascript by 2Tie for OLJ '19
//Deluxe edition by 2Tie for REJ '24

// import * as webio from "./webio.ts";
import * as web_control from "./web_control.ts";
import * as g from "./globals.ts";

export var g_cmds = [
  // 0
  function () {
    g.g.reg16 = get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 1
  function () {
    // Write register data to the next u16 inst
    g.g.tape[get_and_adv_tape_u16()] = g.g.reg16;
  },

  // 2
  function () {
    g.g.tape[get_and_adv_tape_u16()] = g.g.tape[g.g.reg16];
  },

  // 3
  function () {
    g.g.tape[g.g.reg16] = get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 4
  function () {
    g.g.reg16 += get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 5
  function () {
    g.g.reg16 -= get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 6
  function () {
    g.g.cond_reg = g.g.reg16 == get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 7
  function () {
    g.g.cond_reg = g.g.reg16 < get_and_adv_tape_u16_and_load_on_odd_caller();
  },
  // 8
  function () {
    g.g.cond_reg = 0 != (g.g.reg16 & get_and_adv_tape_u16_and_load_on_odd_caller());
  },

  // 9
  function () {
    g.g.reg16 = g.g.reg16 & get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 10
  function () {
    g.g.reg16 = g.g.reg16 | get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 11
  function () {
    g.g.reg16 = g.g.reg16 ^ get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 12
  function () {
    g.g.pc16 = get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 13
  function () {
    var v = get_and_adv_tape_u16_and_load_on_odd_caller();
    g.g.pc16 = g.g.cond_reg ? v : g.g.pc16;
  },

  // 14
  function () {
    var v = get_and_adv_tape_u16_and_load_on_odd_caller();
    g.g.pc16 = g.g.cond_reg ? g.g.pc16 : v;
  },

  // 15
  function () {
    g.g.sp16 -= 1;
    g.g.tape[g.g.sp16] = g.g.pc16 + 2;
    g.g.pc16 = get_and_adv_tape_u16_and_load_on_odd_caller();
  },

  // 16
  function () {
    g.g.pc16 = g.g.tape[g.g.sp16];
    g.g.sp16 += 1;
  },

  // 17
  function () {
    g.g.sp16 -= 1;
    g.g.tape[g.g.sp16] = g.g.reg16;
  },

  // 18
  function () {
    g.g.reg16 = g.g.tape[g.g.sp16];
    g.g.sp16 += 1;
  },

  // 19
  function () {
    g.g.new_frame = 1;
  },

  // 20
  function () {
    g.g.inp = 0;
    g.g.inp +=
      g.g.joyp[37] +
      (g.g.joyp[39] << 1) +
      (g.g.joyp[38] << 2) +
      (g.g.joyp[40] << 3) +
      (g.g.joyp[90] << 4) +
      (g.g.joyp[88] << 5);
    g.g.reg16 = g.g.inp;
  },

  // 21
  function () {
    // Function`$${"\x61 \x3D\x20\x6E\x65\x77 \x44\x61\x74\x65\x28\x29\x5B\x27\x67\x65\x74\x53\x65\x63\x6F\x6E\x64\x73\x27\x5D\x28\x29 "}$`();
    // Hex for:
    // a = new Date()['getSeconds']()

    g.g.reg16 = new Date()['getSeconds']()
  },

  // 22
  function () {
    this.document.location.href = "" + l(g.g.reg16) + ".html";
  },
];

function get_and_adv_tape() {
  var v = g.g.tape[g.g.pc16];
  g.g.pc16 += 1;
  return v;
}

function get_and_adv_tape_u16() {
  var v = get_and_adv_tape();
  return v + (get_and_adv_tape() << 8);
}

function get_and_adv_tape_u16_and_load_on_odd_caller() {
  var inst16 = get_and_adv_tape_u16();
  if (g.g.inst8 % 2 > 0) inst16 = g.g.tape[inst16] || 0;
  return inst16;
}

function l(v) {
  function y(v) {
    return "wnesai0123456789X".substring(v, v + 1);
  }

  var y1 = "";

  while (g.g.tape[v] != 255) {
    y1 = y1 + y(g.g.tape[v]);
    v += 1;
  }

  v += 1;

  var y2 = "";

  while (g.g.tape[v] != 255) {
    y2 = y2 + y(g.g.tape[v]);
    v += 1;
  }

  return y1 + y2;
}

g.g.joyp[37] = 0;
g.g.joyp[38] = 0;
g.g.joyp[39] = 0;
g.g.joyp[40] = 0;
g.g.joyp[88] = 0;
g.g.joyp[90] = 0;

window.onkeyup = function (e: KeyboardEvent) {
  g.g.joyp[e.keyCode] = 0;
};

window.onkeydown = function (e: KeyboardEvent) {
  g.g.joyp[e.keyCode] = 1;
};

// var g.g.socket = webio.connect("localhost", 3003, (event) => {
//   console.log(`Server: ${event.data}`)
// })

web_control.verify_tape_integrity()

web_control.start();


// Starts out onload in html
export function mainloop() {
  g.g.new_frame = 0;
  g.g.inp = 0;

  // var i = 0;

  while (g.g.new_frame == 0) {
    g.g.inst8 = get_and_adv_tape();

    var cmd_idx = Math.floor(g.g.inst8 / 2);

    // if (webio.m_connected) {
    //   g.g.socket.send(`${i++},${cmd_idx},${g.g.data_cur},${g.g.inst8}`)
    // }

    var fn = g_cmds[cmd_idx];
    if (fn) {
      fn();
    } 
  }

  if (!g.g.mq) {
    throw new TypeError('Error message');
  }

  // update black box with the input currently selected if any
  g.g.mq.innerHTML = " ";
  g.g.mq.innerHTML += ((g.g.inp >> 0) & 1) != 0 ? "L" : " ";
  g.g.mq.innerHTML += ((g.g.inp >> 1) & 1) != 0 ? "R" : " ";
  g.g.mq.innerHTML += ((g.g.inp >> 2) & 1) != 0 ? "F" : " ";
  g.g.mq.innerHTML += ((g.g.inp >> 3) & 1) != 0 ? "B" : " ";
  g.g.mq.innerHTML += ((g.g.inp >> 4) & 1) != 0 ? "I" : " ";
  g.g.mq.innerHTML += ((g.g.inp >> 5) & 1) != 0 ? "U" : " ";
  g.g.mq.innerHTML += " ";

  web_control.on_update()

  requestAnimationFrame(mainloop);
}
