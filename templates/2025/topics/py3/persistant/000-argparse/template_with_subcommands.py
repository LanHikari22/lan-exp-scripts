import sys
import os
import argparse

def app_subc1(args: argparse.Namespace):
    print("subcommand1")
    print(args)

def app_subc2(args: argparse.Namespace):
    print("subcommand1")
    print(args)

def main(args: argparse.Namespace):
    if args.subcommand == 'subc1':
        app_subc1(args)
    if args.subcommand == 'subc2':
        app_subc1(args)


def parse_cmdline_args() -> argparse.Namespace:
    desc = '''
    TODO Put tool description here
    '''

    p = argparse.ArgumentParser(prog='TODO', description=desc,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    
    p.add_argument('-v', '--verbose', action='count', default=0,
                   help='Increase verbosity level (use -v, -vv, or -vvv)')
                   
    subparsers = p.add_subparsers(dest='subcommand')
    subparsers.required = True

    sp = subparsers.add_parser('subc1', 
                               help='Subcommand1')
    sp.add_argument('some_primary_arg',
                    help='This is required because...')
    sp.add_argument('-o', '--output', type=str, required=False, 
                    help='Optional str argument with long and short form')
    sp.add_argument('--no-feature', required=False, action='store_true',
                    help='Optional boolean check option')

    sp = subparsers.add_parser('subc2', 
                               help='Subcommand2')

    sp.add_argument('-f', '--format', type=str, required=True, 
                    choices=['ChoiceA', 'ChoiceB'],
                    help=f'Make a choice!')

    # Redirect to a rust application!
    sp = subparsers.add_parser('rust', 
                               help='Redirect to a rust executable')

    sp = subparsers.add_parser('unittest', 
                    help='run the unit tests instead of main')

    return(p.parse_args())

def _main():
    if sys.version_info<(3,5,0):
        sys.stderr.write("You need python 3.5 or later to run this script\n")
        sys.exit(1)

    # if you have unittest as part of the script, you can forward to it this way
    if len(sys.argv) > 1 and sys.argv[1] == 'rust':
        if len(sys.argv) > 2:
            os.system("my-rust-app {}".format(' '.join(sys.argv[2:])))
        else:
            os.system("my-rust-app")

        exit(0)

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

class Module2UnitTests(unittest.TestCase):
   def test_something(self) -> None:
       self.assertTrue(True, "rigorous test :)")


if __name__ == '__main__':
    _main()
