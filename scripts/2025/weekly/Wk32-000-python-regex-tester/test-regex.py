import sys
import os
import argparse
import re

def main(args: argparse.Namespace):
    regex = args.regex
    s = args.s

    print(regex)
    print(s)

    r = re.compile(regex)

    match = re.match(s)

    if match is None:
        print("None")
    else:
        print(match)

def parse_cmdline_args() -> argparse.Namespace:
    desc = '''
    Tests regex strings against text strings in python
    '''

    p = argparse.ArgumentParser(prog='test-regex', description=desc,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    
    p.add_argument('-v', '--verbose', action='count', default=0,
                   help='Increase verbosity level (use -v, -vv, or -vvv)')
    p.add_argument('regex',
                    help='The regex pattern to test')
    p.add_argument('s',
                    help='The string to match against')
                   
    return(p.parse_args())

def _main():
    if sys.version_info<(3,5,0):
        sys.stderr.write("You need python 3.5 or later to run this script\n")
        sys.exit(1)

    # if you have unittest as part of the script, you can forward to it this way
    if len(sys.argv) >= 2 and sys.argv[1] == 'unittest':
        import unittest
        sys.argv[0] += ' unittest'
        sys.argv.remove('unittest')
        print(sys.argv)
        unittest.main()
        exit(0)

    args = parse_cmdline_args()
    return main(args)


import unittest
class Module1UnitTests(unittest.TestCase):
   def test_something(self) -> None:
       self.assertTrue(True, "rigorous test :)")

if __name__ == '__main__':
    _main()
