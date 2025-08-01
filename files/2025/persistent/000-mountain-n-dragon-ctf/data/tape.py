from typing import List, Optional, Tuple
from dataclasses import dataclass
import sys
import os
import argparse
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
    CommandData("cmd00", 0, "cmd00_write_param_to_reg(/*param16*/ {PARAM0})", [16]),
    CommandData(
        "cmd01", 2, "cmd01_store_reg_to_tape_addr(/*tape_addr16*/ {PARAM0})", [16]
    ),
    CommandData("cmd04", 8, "cmd04_sum_reg_param_to_reg(/*param16*/ {PARAM0})", [16]),
    CommandData(
        "cmd06", 12, "cmd06_check_reg16_is_param16(/*param16*/ {PARAM0})", [16]
    ),
    CommandData("cmd13", 26, "cmd13_beq(/*tape_addr16*/ {PARAM0})", [16]),
    CommandData(
        "cmd15", 30, "cmd15_stack_preserve_call(/*tape_addr16*/ {PARAM0})", [16]
    ),
    CommandData("cmd23", 46, "cmd23_noop()", []),
]


def scan_next_command(
    tape: List[int],
) -> Tuple[Optional[Tuple[CommandData, List[int]]], List[int]]:
    """
    returns (
        optional_command_data_tup: This includes the command data and parsed list of params
        remaining_tape: The remaining tape after scanning one command
      )
    """

    # If the tape is empty, nothing to do
    if len(tape) == 0:
        return (None, tape)

    # Read the first byte and route
    command_byte = tape[0]

    command = (
        commands
        | pipe.OfIter[CommandData].filter(
            lambda command: command.activation_byte == command_byte
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
            assert f"unsupported width {width}"

    values_read = (
        command.param_widths
        | pipe.OfIter[int].enumerate()
        | pipe.OfIter[Tuple[int, int]].map(
            pipe.tup2_unpack(enumerated_param_width_to_read_value)
        )
        | pipe.OfIter[int].to_list()
    )

    indices_to_skip = sum(command.param_widths) | pipe.Of[int].map(lambda sum: sum // 8)

    return ((command, values_read), tape[1 + indices_to_skip :])


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


def format_command(command: CommandData, params: List[int]) -> str:
    params_s = format_command_params(command, params)

    mut_result = command.format

    for i, param_s in enumerate(params_s):
        mut_result = mut_result.replace("{PARAM" + str(i) + "}", param_s)

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
    
    print('Created autogen/remaining_tape.ts')


def app_reconstruct_tape():
    tape = read_tape_data()

    content = 'import * as c from "../reconstructed_commands.ts"\n'
    content += 'import * as remaining_tape from "./remaining_tape.ts";\n\n'

    content += "export function reconstruct_tape(): number[] {\n"
    content += "  var tape: number[] = [];\n\n"

    mut_commands: List[Tuple[CommandData, List[int]]] = []
    mut_remaining_tape = tape

    while True:
        command_tup, mut_remaining_tape = scan_next_command(mut_remaining_tape)
        if command_tup is None:
          break

        mut_commands.append(command_tup)

    for command, params in mut_commands:
      command_s = format_command(command, params)

      content += f'  tape.push(...c.{command_s});\n'

    content += "  tape.push(...remaining_tape.data);\n\n"
    content += "  return tape;\n"
    content += "}"

    create_remaining_tape_ts(mut_remaining_tape)

    with open(f"{script_path}/../autogen/reconstructed_tape.ts", "w") as f:
        f.write(content)
    
    print('Created autogen/reconstructed_tape.ts')



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
