import * as reconstructed_tape from './autogen/reconstructed_tape.ts'

export const g = {
  inp: 0,
  mq: document.getElementById("marquee"),
  cond_reg: false,
  reg16: 0,
  pc16: 0,
  sp16: 0,
  inst8: 0,
  new_frame: 0,
  tape: reconstructed_tape.reconstruct_tape(),
  joyp: {},
};


// export var inp = 0;
// export var mq = document.getElementById("marquee");

// export var cond_reg = false;

// export var reg16 = 0,
//   pc16 = 0,
//   sp16 = 0,
//   inst8 = 0,
//   new_frame = 0;

// export var tape = reconstructed_tape.reconstruct_tape();

// export var joyp = {};
