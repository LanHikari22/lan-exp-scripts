from typing import List, Optional, Tuple
from dataclasses import dataclass
import sys
import os
import argparse
import time
import checkpipe as pipe

script_path = os.path.dirname(os.path.realpath(__file__))


def read_tape_data() -> List[int]:
    with open(f"{script_path}/tape.txt", "r") as f:
        result = (
            f.read()
            | pipe.Of[str].map(lambda s: s.split(","))
            | pipe.OfIter[str].filter(lambda s: s.strip() != "")
            | pipe.OfIter[str].map(lambda s: int(s))
            | pipe.OfIter[int].to_list()
        )

        return result


def app_display_tape_stats():
    tape = read_tape_data()
    print("checksum", sum(tape))
    print("#", len(tape))


@dataclass
class CommandData:
    name: str
    activation_byte: int
    format: str
    """this should have placeholders for each param tagged {PARAM#} where # is the nth param."""
    param_widths: List[int]
    """Specifies the number of params in the format placeholder and the sizes of each"""


commands = [
    CommandData("cmd00", 0, "cmd00_write_param16_to_reg16(/*param16*/ {PARAM0})", [16]),
    CommandData(
        "cmd01", 2, "cmd01_store_reg16_to_tape_addr(/*addr16*/ {PARAM0})", [16]
    ),
    CommandData(
        "cmd02",
        4,
        "cmd02_store_loaded_reg16_to_loaded_param16(/*addr16*/ {PARAM0})",
        [16],
    ),
    CommandData(
        "cmd03", 6, "cmd03_set_loaded_reg16_to_param16(/*param16*/ {PARAM0})", [16]
    ),
    CommandData(
        "cmd04", 8, "cmd04_sum_reg16_param16_to_reg16(/*param16*/ {PARAM0})", [16]
    ),
    CommandData(
        "cmd05", 10, "cmd05_sub_param16_from_reg16(/*param16*/ {PARAM0})", [16]
    ),
    CommandData(
        "cmd06", 12, "cmd06_check_reg16_is_param16(/*param16*/ {PARAM0})", [16]
    ),
    CommandData(
        "cmd07", 14, "cmd07_check_reg16_lt_param16(/*param16*/ {PARAM0})", [16]
    ),
    CommandData(
        "cmd08", 16, "cmd08_check_reg16_and_param16(/*param16*/ {PARAM0})", [16]
    ),
    CommandData(
        "cmd09", 18, "cmd09_mask_reg16_and_param16_to_reg16(/*param16*/ {PARAM0})", [16]
    ),
    CommandData(
        "cmd10", 20, "cmd10_check_reg16_or_param16(/*param16*/ {PARAM0})", [16]
    ),
    CommandData(
        "cmd11", 22, "cmd11_check_reg16_xor_param16(/*param16*/ {PARAM0})", [16]
    ),
    CommandData("cmd12", 24, "cmd12_goto(/*addr16*/ {PARAM0})", [16]),
    CommandData("cmd13", 26, "cmd13_beq(/*addr16*/ {PARAM0})", [16]),
    CommandData("cmd14", 28, "cmd14_bne(/*addr16*/ {PARAM0})", [16]),
    CommandData("cmd15", 30, "cmd15_stack_preserve_call(/*addr16*/ {PARAM0})", [16]),
    CommandData("cmd16", 32, "cmd16_return()", []),
    CommandData("cmd17", 34, "cmd17_push_reg16_to_stack()", []),
    CommandData("cmd18", 36, "cmd18_pop_stack_to_reg16()", []),
    CommandData("cmd19", 38, "cmd19_issue_new_frame()", []),
    CommandData("cmd20", 40, "cmd20_read_joypad_input_and_set_to_reg16()", []),
    CommandData("cmd21", 42, "cmd21_set_reg16_to_cur_seconds()", []),
    CommandData("cmd22", 44, "cmd22_set_dom_href_to_reg16()", []),
    CommandData("cmd23", 46, "cmd23_noop()", []),
    CommandData("cmd25", 50, "cmd25_bug()", []),
]


def compute_num_command_bytes(command: CommandData):
    return sum(command.param_widths) | pipe.Of[int].map(lambda sum: sum // 8)


def scan_next_command(
    tape: List[int],
) -> Tuple[Optional[Tuple[CommandData, List[int]]], List[int]]:
    """
    returns (
        optional_command_data_tup: This includes the command data and the parsed binary content
        remaining_tape: The remaining tape after scanning one command
      )
    """

    # If the tape is empty, nothing to do
    if len(tape) == 0:
        return (None, tape)

    # Read the first byte and route
    command_byte = tape[0]

    def activation_byte_matches(activation_byte: int, command_byte: int) -> bool:
        assert activation_byte % 2 == 0

        return command_byte == activation_byte or command_byte == activation_byte + 1

    command = (
        commands
        | pipe.OfIter[CommandData].filter(
            lambda command: activation_byte_matches(
                command.activation_byte, command_byte
            )
        )
        | pipe.OfIter[CommandData].to_list()
        | pipe.Of[List[CommandData]].map(lambda lst: lst[0] if len(lst) == 1 else None)
    )

    if command is None:
        return (None, tape)

    # Now read the bytes according to the command's parameters

    def enumerated_param_width_to_read_value(i: int, width: int) -> int:
        if width == 16:
            return (tape[i + 2] << 8) + tape[i + 1]
        elif width == 8:
            return tape[i + 1]
        else:
            raise Exception(f"unsupported width {width}")

    content = (
        [command_byte] + (command.param_widths
        | pipe.OfIter[int].enumerate()
        | pipe.OfIter[Tuple[int, int]].map(
            pipe.tup2_unpack(enumerated_param_width_to_read_value)
        )
        | pipe.OfIter[int].to_list())
    )

    return ((command, content), tape[1 + compute_num_command_bytes(command) :])


def format_command_params(command: CommandData, params: List[int]) -> List[str]:
    assert len(command.param_widths) == len(params)

    def width_n_to_formatted(width: int, n: int) -> str:
        if width == 16:
            return f"0x{n:04x}"
        elif width == 8:
            return f"0x{n:02x}"
        else:
            assert f"unsupported width {width}"

    formatted_params = (
        command.param_widths
        | pipe.OfIter[int].zip(params)
        | pipe.OfIter[Tuple[int, int]].map(pipe.tup2_unpack(width_n_to_formatted))
        | pipe.OfIter[str].to_list()
    )

    return formatted_params


def format_command(command: CommandData, content: List[int]) -> str:
    assert len(content) >= 1

    command_byte = content[0]
    params_s = format_command_params(command, content[1:])

    mut_result = command.format

    for i, param_s in enumerate(params_s):
        mut_result = mut_result.replace("{PARAM" + str(i) + "}", param_s)
    
    if command_byte % 2 == 1:
        mut_result = mut_result.replace("cmd", "cmdl")

    return mut_result


def create_remaining_tape_ts(remaining_tape: List[int]):
    content = "export var data = [\n"

    for i, elem in enumerate(remaining_tape):
        content += f"{elem}, "
        if i % 21 == 0 and i != 0:
            content += "\n"

    content += "\n];"

    with open(f"{script_path}/../autogen/remaining_tape.ts", "w") as f:
        f.write(content)

    print("Created autogen/remaining_tape.ts")


def compute_program_counter(commands: List[CommandData], i: int) -> int:
    mut_result = 0

    for j, command in enumerate(commands):
        if j == i:
            break

        mut_result += 1 + compute_num_command_bytes(command)

    return mut_result


def app_reconstruct_tape():
    start = time.time()

    tape = read_tape_data()

    mut_content = 'import * as c from "../reconstructed_commands.ts"\n'
    mut_content += 'import * as remaining_tape from "./remaining_tape.ts";\n\n'

    mut_content += "export function reconstruct_tape(): number[] {\n"
    mut_content += "  var tape: number[] = [];\n\n"

    mut_content_csv = "pc16,cmd,name,cmd_byte,param,byte1,byte2,format\n"

    mut_commands: List[Tuple[CommandData, List[int]]] = []
    mut_remaining_tape = tape

    while True:
        command_tup, mut_remaining_tape = scan_next_command(mut_remaining_tape)
        if command_tup is None:
            break

        mut_commands.append(command_tup)

    raw_commands = (
        mut_commands
        | pipe.OfIter[Tuple[CommandData, List[int]]].map(
            pipe.tup2_unpack(lambda command, _: command)
        )
        | pipe.OfIter[CommandData].to_list()
    )

    for i, (command, command_content) in enumerate(mut_commands):
        command_s = format_command(command, command_content)
        pc = compute_program_counter(raw_commands, i)

        name = (
            command_s
            | pipe.Of[str].map(lambda s: s.split('(')[0])
        )

        mut_content += f"  /*0x{pc:04x}*/ tape.push(...c.{command_s});\n"

        if len(command_content) == 1:
            mut_content_csv += f'0x{pc:04x},{command.name},{name},{command_content[0]},-1,-1,-1,{command_s}\n'
        else:
            byte1 = command_content[1] & 0x00FF
            byte2 = (command_content[1] & 0xFF00) >> 8
            mut_content_csv += f'0x{pc:04x},{command.name},{name},{command_content[0]},{command_content[1]},{byte1},{byte2},{command_s}\n'

    mut_content += "  tape.push(...remaining_tape.data);\n\n"
    mut_content += "  return tape;\n"
    mut_content += "}"

    create_remaining_tape_ts(mut_remaining_tape)

    with open(f"{script_path}/../autogen/reconstructed_tape.ts", "w") as f:
        f.write(mut_content)

    with open(f"{script_path}/../experiments/tape_program_data.csv", "w") as f:
        f.write(mut_content_csv)

    end = time.time()

    print(f'Created autogen/reconstructed_tape.ts in {end-start} seconds')


def main(args: argparse.Namespace):
    if args.subcommand == "display-tape-stats":
        app_display_tape_stats()
    if args.subcommand == "reconstruct-tape":
        app_reconstruct_tape()


def parse_cmdline_args() -> argparse.Namespace:
    desc = """
    Tape data manipulation script
    """

    p = argparse.ArgumentParser(
        prog="tape",
        description=desc,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    p.add_argument(
        "-v",
        "--verbose",
        action="count",
        default=0,
        help="Increase verbosity level (use -v, -vv, or -vvv)",
    )

    subparsers = p.add_subparsers(dest="subcommand")
    subparsers.required = True

    sp = subparsers.add_parser(
        "display-tape-stats", help="Show some information about the tape data"
    )

    sp = subparsers.add_parser(
        "reconstruct-tape",
        help="Reconstruct a typescript function with commands that produce the tape",
    )

    sp = subparsers.add_parser("unittest", help="run the unit tests instead of main")

    return p.parse_args()


def _main():
    if sys.version_info < (3, 5, 0):
        sys.stderr.write("You need python 3.5 or later to run this script\n")
        sys.exit(1)

    # if you have unittest as part of the script, you can forward to it this way
    if len(sys.argv) >= 2 and sys.argv[1] == "unittest":
        import unittest

        sys.argv[0] += " unittest"
        sys.argv.remove("unittest")
        print(sys.argv)
        unittest.main()
        exit(0)

    args = parse_cmdline_args()
    return main(args)


from typing import List
import unittest


class Module1UnitTests(unittest.TestCase):
    def test_something(self) -> None:
        self.assertTrue(True, "rigorous test :)")


class Module2UnitTests(unittest.TestCase):
    def test_something(self) -> None:
        self.assertTrue(True, "rigorous test :)")


if __name__ == "__main__":
    _main()
