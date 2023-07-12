#! /usr/bin/env python3

# --------------------------------------------------------------------
import csv
import math
import os
import re

from prerequisite import core

#-----------------------------------------------------------------------
def optparser():
    import argparse as argp

    parser = argp.ArgumentParser(
      description = 'Read dune/coq logs and extract timing information'
    )
    parser.add_argument('name', help = 'The polytope name')
    parser.add_argument('--hirsch', help = 'Treat the case where the polytope is a Hirsch-CounterExample', action="store_true")
    parser.add_argument('--time', help = 'Read the global.log of a polytope', action="store_true")
    return parser

#-----------------------------------------------------------------------
def readlog_cumulated(logfile):

    # rheader = r'^coqc.*,[^/]*(.*?)\.\{glob,vo\}'
    # rcoqc = r'^Chars \d+ - \d+ \[.*?\] (\d+\.\d*) secs'
    rwrapper = r"^(\d+,\d*)s"
    # coqcs = 0
    wrappers = 0

    with open(logfile) as stream:
        for line in stream:
            line = line.strip()

            # def bailout():
            #     raise ValueError(f'invalid log file: {logfile}:{lineno} ({line})')

            # if (m := re.search(rcoqc, line)):
            #     coqcs += float(m.group(1))
            if (m := re.search(rwrapper,line)):
                wrappers += float(m.group(1).replace(",","."))
            else:
                pass

    return wrappers

def readlog_global(logfile):
    rtime = r'^dune build .*? cpu (\d+:?\d*:?\d*,\d*) total'
    time_global = None
    with open(logfile) as stream:
        for line in stream:
            if (m := re.search(rtime,line)):
                return m.group(1)

#-----------------------------------------------------------------------
def handle_time_output(time_output):
    minutes = time_output.split(":")
    minutes.reverse()
    seconds = float(minutes[0].replace(",", "."))
    a = 60
    for elt in minutes[1:]:
        seconds += float(elt) * a
        a *= 60
    return seconds

#-----------------------------------------------------------------------
def cumulated(name,hirsch):
    jobs = ["coq", "Validation", "Diameter"] if not hirsch else ["coq", "Validation", "Hirsch", "Exact"]
    res_wrappers = f"{name}"
    for job in jobs:
        wrappers = readlog_cumulated(core.resource(name, f'{job}.log'))
        if job == "Hirsch":
            wrappers = f"({wrappers})"
        res_wrappers += f', {wrappers}'
    print(f"{res_wrappers}")

def global_time(name):
    time_global = readlog_global(core.resource(name,'global.log'))
    print(name, ' | ', time_global, ' | ', handle_time_output(time_global))

    

def main():
    args = optparser().parse_args()
    if args.time: 
        global_time(args.name)
    else:
        cumulated(args.name, args.hirsch)


# --------------------------------------------------------------------
if __name__ == '__main__':
    main()
