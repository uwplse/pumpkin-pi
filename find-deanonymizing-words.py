import sys
import subprocess
import re

grep_line_re = re.compile(r'^(.*):(\d+):(.*)')

def grep_for_substr(s, root, casesensitive=True, exclude=None):
    try:
        args = ['grep', '-Rn', '--color=never']
        if exclude:
            args.append(f'--exclude-dir={exclude!s}')
        if not casesensitive:
            args.append('-i')
        cp = subprocess.run([*args, s, root], capture_output=True)
        lines = str(cp.stdout, 'utf-8').split('\n')
    except Exception:
        print(f'!! Irregularity searching for {s!r} in {root!r}')
        lines = []
    return lines

def merge_lines(lines):
    locations = {}
    for line in lines:
        m = grep_line_re.match(line)
        if m:
            fname, lineno, words = m.group(1), int(m.group(2)), m.group(3)
            if fname in locations:
                locations[fname][lineno] = words
            else:
                locations[fname] = {lineno:words}
    return locations

def describe_locations(locations):
    for fname in sorted(locations.keys()):
        print(f'{fname!s}:')
        descrs = []
        digits = 0
        for lineno in sorted(locations[fname].keys()):
            descrs.append((str(lineno), locations[fname][lineno]))
            digits = max(digits, len(str(lineno)))
        for nstr, words in descrs:
            print(f'  {nstr}{" "*(digits - len(nstr))}: {words}')
        print(flush=True)

def main(root, substrs, casesensitive=True, exclude=None):
    lines = []
    for s in substrs:
        lines += grep_for_substr(s, root, casesensitive=casesensitive, exclude=exclude)
    locations = merge_lines(lines)
    describe_locations(locations)


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=str, default='.',
                        help='root directory to grep in')
    parser.add_argument('--exclude', type=str, default='',
                        help='--exclude-dir for grep')
    parser.add_argument('-i', action='store_true',
                        help='case insensitive (-i argument for grep)')
    parser.add_argument('--list', type=str, default='',
                        help='read substrings from file')
    parser.add_argument('substrs', type=str, nargs='*',
                        help='additional substrings to search for')

    args = parser.parse_args()
    substrs = []
    if args.list:
        with open(args.list, 'rt') as f:
            for line in f:
                substr = line.strip()
                if substr:
                    substrs.append(substr)

    if args.substrs:
        for substr in args.substrs:
            if substr:
                substrs.append(substr)

    if args.exclude:
        exclude = args.exclude
    else:
        exclude = None

    main(args.root, substrs, casesensitive=(not args.i), exclude=exclude)
