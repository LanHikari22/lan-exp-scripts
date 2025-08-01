import * as c from "../reconstructed_commands.ts"
import * as remaining_tape from "./remaining_tape.ts";

export function reconstruct_tape(): number[] {
  var tape: number[] = [];

  tape.push(...c.cmd00_write_param_to_reg(/*param16*/ 0x0000));
  tape.push(...c.cmd01_store_reg_to_tape_addr(/*tape_addr16*/ 0x33af));
  tape.push(...c.cmd01_store_reg_to_tape_addr(/*tape_addr16*/ 0x33b3));
  tape.push(...c.cmd01_store_reg_to_tape_addr(/*tape_addr16*/ 0x33b4));
  tape.push(...c.cmd01_store_reg_to_tape_addr(/*tape_addr16*/ 0x33b6));
  tape.push(...c.cmd04_sum_reg_param_to_reg(/*param16*/ 0x0001));
  tape.push(...c.cmd01_store_reg_to_tape_addr(/*tape_addr16*/ 0x33b7));
  tape.push(...c.cmd00_write_param_to_reg(/*param16*/ 0x0c8c));
  tape.push(...c.cmd23_noop());
  tape.push(...c.cmd00_write_param_to_reg(/*param16*/ 0x0d22));
  tape.push(...c.cmd23_noop());
  tape.push(...c.cmd15_stack_preserve_call(/*tape_addr16*/ 0x0bb0));
  tape.push(...c.cmd06_check_reg16_is_param16(/*param16*/ 0x0000));
  tape.push(...c.cmd13_beq(/*tape_addr16*/ 0x038a));
  tape.push(...c.cmd06_check_reg16_is_param16(/*param16*/ 0x0002));
  tape.push(...c.cmd13_beq(/*tape_addr16*/ 0x0059));
  tape.push(...c.cmd06_check_reg16_is_param16(/*param16*/ 0x0001));
  tape.push(...c.cmd13_beq(/*tape_addr16*/ 0x046a));
  tape.push(...c.cmd06_check_reg16_is_param16(/*param16*/ 0x0003));
  tape.push(...c.cmd13_beq(/*tape_addr16*/ 0x016a));
  tape.push(...c.cmd06_check_reg16_is_param16(/*param16*/ 0x0005));
  tape.push(...c.cmd13_beq(/*tape_addr16*/ 0x0044));
  tape.push(...c.cmd15_stack_preserve_call(/*tape_addr16*/ 0x0ac5));
  tape.push(...remaining_tape.data);

  return tape;
}