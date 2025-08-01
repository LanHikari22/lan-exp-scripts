export function cmd00_write_param16_to_reg16(param16: number): number[] {
  return [0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd00_write_loaded_param16_to_reg16(param16: number): number[] {
  return [1, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd01_store_reg16_to_tape_addr(addr16: number): number[] {
  return [2, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd02_store_loaded_reg16_to_loaded_param16(addr16: number): number[] {
  return [4, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd03_set_loaded_reg16_to_param16(param16: number): number[] {
  return [6, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd03_set_loaded_reg16_to_loaded_param16(addr16: number): number[] {
  return [7, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd04_sum_reg16_param16_to_reg16(param16: number): number[] {
  return [8, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd04_sum_reg16_loaded_param16_to_reg16(param16: number): number[] {
  return [9, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd05_sub_param16_from_reg16(param16: number): number[] {
  return [10, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd06_check_reg16_is_param16(param16: number): number[] {
  return [12, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd06_check_reg16_is_loaded_param16(param16: number): number[] {
  return [13, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd07_check_reg16_lt_param16(param16: number): number[] {
  return [14, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd07_check_reg16_lt_loaded_param16(addr16: number): number[] {
  return [15, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd09_check_reg16_and_param16(param16: number): number[] {
  return [18, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd12_goto(addr16: number): number[] {
  return [24, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd13_beq(addr16: number): number[] {
  return [26, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd14_bne(addr16: number): number[] {
  return [28, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd15_stack_preserve_call(addr16: number): number[] {
  return [30, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}
export function cmd16_return(): number[] {
  return [32];
}

export function cmd17_push_reg16_to_stack(): number[] {
  return [34];
}

export function cmd18_pop_stack_to_reg16(): number[] {
  return [36];
}

export function cmd19_issue_new_frame(): number[] {
  return [38];
}

export function cmd20_read_joypad_input_and_set_to_reg16(): number[] {
  return [40];
}

export function cmd21_set_reg16_to_cur_seconds(): number[] {
  return [42];
}

export function cmd22_set_dom_href_to_reg16(): number[] {
  return [44];
}

export function cmd23_noop(): number[] {
  return [46];
}
