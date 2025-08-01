export function cmd00_write_param_to_reg(param16: number): number[] {
  return [0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd01_store_reg_to_tape_addr(tape_addr16: number): number[] {
  return [2, tape_addr16 & 0xFF, (tape_addr16 & 0xFF00) >> 8];
}

export function cmd04_sum_reg_param_to_reg(param16: number): number[] {
  return [8, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd06_check_reg16_is_param16(param16: number): number[] {
  return [12, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd13_beq(tape_addr16: number): number[] {
  return [26, tape_addr16 & 0xFF, (tape_addr16 & 0xFF00) >> 8];
}

export function cmd15_stack_preserve_call(tape_addr16: number): number[] {
  return [30, tape_addr16 & 0xFF, (tape_addr16 & 0xFF00) >> 8];
}

export function cmd23_noop(): number[] {
  return [46];
}
