#!/bin/python3

# bn_lexer_ron2csv.py
import sys
import csv
import re
import os

# Regular expression to match RON-style tuple entries
ron_re = re.compile(
    r'''
    ^\(
    \s*lexon_type:\s*([^\s,]+),\s*
    lexon_data:\s*([^\s,]+(?:\(".*?"\))?),\s*
    capture:\s*("(?:[^"\\]|\\.)*?")
    \s*\)
    ''',
    re.VERBOSE,
)

# Matches FILENAME directive line
filename_re = re.compile(r'^FILENAME\s+(.+)$')

def strip_filename(path):
    """Return path relative to the last occurrence of 'lexer/'"""
    parts = path.split('lexer/')
    return parts[-1] if len(parts) > 1 else os.path.basename(path)

def parse_with_filenames(input_lines):
    current_filename = None
    for line in input_lines:
        line = line.rstrip('\n')
        fname_match = filename_re.match(line)
        if fname_match:
            current_filename = strip_filename(fname_match.group(1))
            continue

        ron_match = ron_re.match(line)
        if ron_match and current_filename:
            yield [
                ron_match.group(1),  # lexon_type
                ron_match.group(2),  # lexon_data
                ron_match.group(3),  # capture (escaped as-is)
                current_filename     # simplified filename
            ]

def main():
    reader = sys.stdin
    writer = csv.writer(sys.stdout, quoting=csv.QUOTE_MINIMAL)
    writer.writerow(['lexon_type', 'lexon_data', 'capture', 'filename'])

    for row in parse_with_filenames(reader):
        writer.writerow(row)

if __name__ == "__main__":
    main()
