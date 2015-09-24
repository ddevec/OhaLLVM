#!/usr/bin/python
"""
Parses debug output from SpecSFS
"""

import argparse

def parse_id_map(id_map):
    """
    parses output from PrintID pass returns dict of id to string
    """
    ret = dict()

    with open(id_map, "r") as f:
        have_out = False
        for line in f:
            line = line.strip()

            if line == "OUTPUT:":
                have_out = True
                continue

            if not have_out:
                continue

            words = line.split(":")
            num = int(words[0])
            inst = ''.join(words[1:])

            ret[num] = inst.strip()

    return ret

def main(args):
    """
    Main operation of the tracer
    """
    # First, parse the trace file
    id_map = parse_id_map(args.id_map)

    # Now, parse the trace file
    with open(args.log_file, "r") as f:
        for line in f:
            strip_line = line.strip()
            words = strip_line.split()

            if len(words) == 0:
                print strip_line
            elif words[0] == "rep:":
                rep_val = id_map[int(words[1])]
                print "  rep: (" + words[1] + ") " + rep_val
            elif words[0] == "src:":
                src_val = id_map[int(words[1])]
                print "  src: (" + words[1] + ") " + src_val
                if len(words) > 3:
                    print "    src_set: " + ''.join(words[3:])
            elif words[0] == "dest:":
                dest_val = id_map[int(words[1])]
                print "  dest: (" + words[1] + ") " + dest_val
                if len(words) > 3:
                    print "    dest_set: " + ''.join(words[3:])
            else:
                # Don't print \n char
                print line[:-1]

if __name__ == "__main__":
    parser = argparse.ArgumentParser("Analyze a SpecSFS execution, "+
            "print a trace")
    parser.add_argument("log_file", help="Log file from traceout.py")
    parser.add_argument("id_map", help="Id map from llvm PrintID pass")
    main_args = parser.parse_args()
    main(main_args)

