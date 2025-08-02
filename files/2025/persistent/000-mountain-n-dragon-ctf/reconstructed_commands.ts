export function cmd00_write_param16_to_reg16(param16: number): number[] {
  return [0+0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd01_store_reg16_to_tape_addr(addr16: number): number[] {
  return [2+0, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd02_store_loaded_reg16_to_loaded_param16(addr16: number): number[] {
  return [4+0, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd03_set_loaded_reg16_to_param16(param16: number): number[] {
  return [6+0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd04_sum_reg16_param16_to_reg16(param16: number): number[] {
  return [8+0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd05_sub_param16_from_reg16(param16: number): number[] {
  return [10+0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd06_check_reg16_is_param16(param16: number): number[] {
  return [12+0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd07_check_reg16_lt_param16(param16: number): number[] {
  return [14+0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd08_check_reg16_and_param16(param16: number): number[] {
  return [16+0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd09_mask_reg16_and_param16_to_reg16(param16: number): number[] {
  return [18+0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd10_check_reg16_or_param16(param16: number): number[] {
  return [20+0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd11_check_reg16_xor_param16(param16: number): number[] {
  return [22+0, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmd12_goto(addr16: number): number[] {
  return [24+0, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd13_beq(addr16: number): number[] {
  return [26+0, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd14_bne(addr16: number): number[] {
  return [28+0, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmd15_stack_preserve_call(addr16: number): number[] {
  return [30+0, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}
export function cmd16_return(): number[] {
  return [32+0];
}

export function cmd17_push_reg16_to_stack(): number[] {
  return [34+0];
}

export function cmd18_pop_stack_to_reg16(): number[] {
  return [36+0];
}

export function cmd19_issue_new_frame(): number[] {
  return [38+0];
}

export function cmd20_read_joypad_input_and_set_to_reg16(): number[] {
  return [40+0];
}

export function cmd21_set_reg16_to_cur_seconds(): number[] {
  return [42+0];
}

export function cmd22_set_dom_href_to_reg16(): number[] {
  return [44+0];
}

export function cmd23_noop(): number[] {
  return [46+0];
}

export function cmd25_bug(): number[] {
  return [50+0];
}


// Mirror commands for odd bit

export function cmdl00_write_param16_to_reg16(param16: number): number[] {
  return [0+1, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmdl01_store_reg16_to_tape_addr(addr16: number): number[] {
  return [2+1, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmdl02_store_loaded_reg16_to_loaded_param16(addr16: number): number[] {
  return [4+1, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmdl03_set_loaded_reg16_to_param16(param16: number): number[] {
  return [6+1, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmdl04_sum_reg16_param16_to_reg16(param16: number): number[] {
  return [8+1, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmdl05_sub_param16_from_reg16(param16: number): number[] {
  return [10+1, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmdl06_check_reg16_is_param16(param16: number): number[] {
  return [12+1, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmdl07_check_reg16_lt_param16(param16: number): number[] {
  return [14+1, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmdl08_check_reg16_and_param16(param16: number): number[] {
  return [16+1, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmdl09_mask_reg16_and_param16_to_reg16(param16: number): number[] {
  return [18+1, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmdl10_check_reg16_or_param16(param16: number): number[] {
  return [20+1, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmdl11_check_reg16_xor_param16(param16: number): number[] {
  return [22+1, param16 & 0xFF, (param16 & 0xFF00) >> 8];
}

export function cmdl12_goto(addr16: number): number[] {
  return [24+1, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmdl13_beq(addr16: number): number[] {
  return [26+1, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmdl14_bne(addr16: number): number[] {
  return [28+1, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}

export function cmdl15_stack_preserve_call(addr16: number): number[] {
  return [30+1, addr16 & 0xFF, (addr16 & 0xFF00) >> 8];
}
export function cmdl16_return(): number[] {
  return [32+1];
}

export function cmdl17_push_reg16_to_stack(): number[] {
  return [34+1];
}

export function cmdl18_pop_stack_to_reg16(): number[] {
  return [36+1];
}

export function cmdl19_issue_new_frame(): number[] {
  return [38+1];
}

export function cmdl20_read_joypad_input_and_set_to_reg16(): number[] {
  return [40+1];
}

export function cmdl21_set_reg16_to_cur_seconds(): number[] {
  return [42+1];
}

export function cmdl22_set_dom_href_to_reg16(): number[] {
  return [44+1];
}

export function cmdl23_noop(): number[] {
  return [46+1];
}

export function cmdl25_bug(): number[] {
  return [50+1];
}

