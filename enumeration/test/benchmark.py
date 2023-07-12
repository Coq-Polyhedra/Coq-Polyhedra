#! /usr/bin/env python3

# --------------------------------------------------------------------
import argparse as argp
import subprocess as sp
import os
import re
import time
import math
from scripts import core, lrs2json, json2bin, bin2coq, coqjobs, genlrs
import csv
import shutil

CWD = os.getcwd()
TIME_MEM_PREFIX = r'TIMEFMT="%E : real time, %M : max memory" && '
HIRSCH_CEX = ["poly20dim21","poly23dim24"]
BENCH_DIR = os.path.join(os.getcwd(),"benchmarks")

# --------------------------------------------------------------------

def command_call(command, prefix=""):
  output = sp.run(prefix + command,
            shell=True, executable="/bin/zsh", check=True,
            capture_output=True, text=True)
  print(output.stdout, output.stderr)
  return output.stderr

# --------------------------------------------------------------------
def format_time_output(st):
  findit = re.search(r"\n(\d+,\d+)s.+, (\d+)", st)
  time = findit.group(1).replace(",", ".")
  memory = findit.group(2)
  return time, memory

# --------------------------------------------------------------------
def clean_coq(*args):
  command_call("dune clean")

def theories(*args):
  time, _ = format_time_output(command_call("time dune build " + os.path.join("..","theories"),TIME_MEM_PREFIX))
  return time

# --------------------------------------------------------------------
def polytopes(prefix,nmin,nmax):
  datas = os.listdir(core.resource())
  if prefix == "hirsch":
    for name in datas:
      if name in ["poly20dim21", "poly23dim24"]:
        print(name)
        yield name

  elif prefix != "":
    for name in datas:
      pref_match = re.match(f"{prefix}_(\d+)", name)
      if pref_match is not None and nmin <= int(pref_match.group(1)) <= nmax:
        print(name)
        yield(name) 
  else:
    for name in datas:
      if not name.startswith("."):
        print(name)
        yield name

# --------------------------------------------------------------------

def lrs(prefix,nmin,nmax,compute):
  res = []
  for name in polytopes(prefix,nmin,nmax):
    res.append({"polytope" : name})
    inefile = core.resource(name,"lrs",name+".ine")
    extfile = core.resource(name,"lrs",name+".ext")
    time, memory = format_time_output(command_call(f"time lrs {inefile} {extfile}",TIME_MEM_PREFIX))
    res[-1]["time"], res[-1]["memory"] = time, memory
  return res

# --------------------------------------------------------------------
def certificates(prefix,nmin,nmax,compute):
  res = []
  for name in polytopes(prefix,nmin,nmax):
    res.append({"polytope" : name})
    hirsch = False
    if name in HIRSCH_CEX:
      hirsch = True
    st = time.time()
    dict = lrs2json.lrs2dict(name,hirsch)
    json2bin.dict2bin(name,dict)
    bin2coq.main(name)
    coqjobs.main(name,"Validation",compute)
    if name in ["poly20dim21", "poly23dim24"]:
      coqjobs.main(name,"Hirsch",compute)
      coqjobs.main(name,"Exact",compute)
    else:
      coqjobs.main(name,"Diameter",compute)
    et = time.time()
    res[-1]["time"] = f"{et - st:.2f}"
  return res

# --------------------------------------------------------------------
def compilation(prefix,nmin,nmax,compute):
  res = []
  for name in polytopes(prefix,nmin,nmax):
    res.append({"polytope" : name})
    times = []
    max_memory = -math.inf
    coqdir = core.resource(name,"coq")
    for file in os.listdir(coqdir):
      if file.endswith(".v"):
        print(file)
        rel_path = os.path.join("data",name,"coq",file+"o")
        st = command_call("time dune build " + rel_path,TIME_MEM_PREFIX)
        time, memory = format_time_output(st)
        res[-1][file + " time"] = time
        res[-1][file + " memory"] = memory
        times.append(float(time))
        max_memory = max(max_memory,int(memory))
    res[-1]["cumulated time"] = str(math.fsum(times))
    res[-1]["max memory"] = str(max_memory)
  return res

def job(job):
  def worker(prefix,nmin,nmax,compute):
    res = []
    for name in polytopes(prefix,nmin,nmax):
      jobdir = core.resource(name,f"coq_{job}")
      if not os.path.exists(jobdir):
        continue
      res.append({"polytope" : name})
      times = []
      max_memory = -math.inf
      datas = list(os.listdir(jobdir))
      datas.sort(key=f"{job}.v".__eq__)
      for file in datas:
        if file.endswith(".v"):
          print(file)
          st = command_call("time dune build " + os.path.join("data",name,f"coq_{job}",file+"o"),TIME_MEM_PREFIX)
          time, memory = format_time_output(st)
          res[-1][file + " time"] = time
          res[-1][file + " memory"] = memory
          times.append(float(time))
          max_memory = max(max_memory,int(memory))
      res[-1]["cumulated time"] = str(math.fsum(times))
      res[-1]["max memory"] = str(max_memory)
    return res
  return worker

# --------------------------------------------------------------------
def clean_data(prefix,nmin,nmax,compute):
  for name in polytopes(prefix,nmin,nmax):
    if name not in HIRSCH_CEX:
      shutil.rmtree(core.resource(name))
    else:
      for file in os.listdir(core.resource(name)):
        if file != "lrs":
          shutil.rmtree(core.resource(name,file))
        else:
          path_ext = core.resource(name,file,f"{name}.ext")
          if os.path.exists(path_ext):
            os.remove(path_ext)
# --------------------------------------------------------------------
# --------------------------------------------------------------------
DEF_GEN = {"cube" : (3,13), "cross" : (3,7), "cyclic" : (3,10), "permutahedron" : (3,7)}
def gen(prefix,nmin,nmax,compute):
  if prefix != "":
    polytopes = {prefix : (nmin, nmax)}
  else:
    polytopes = DEF_GEN
  for poly, (n, N) in polytopes.items():
    for k in range(n, N+1):
      if poly == "cyclic":
        genlrs.generate_lrs(poly, 2*k, k)
      else:
        genlrs.generate_lrs(poly, k)
# --------------------------------------------------------------------
def writer(stream):
  def output(st):
    print(st,file=stream)
  return output

def bench2csv(kind,res):
  taskdir = os.path.join(BENCH_DIR,kind)
  os.makedirs(taskdir,exist_ok=True)
  file_name = f"{kind}_" + time.strftime("%m-%d-%H-%M-%S") + (".log" if kind == "theories" else ".csv")
  taskfile = os.path.join(taskdir, file_name)
  with open(taskfile, "w", newline='') as stream:
    output = writer(stream)
    if kind == "theories":
      output(f"Compilation of theories time : {res}")
    else:
      if res != []:
        idx = max(range(len(res)), key = (lambda i : len(res[i])))
        measured = list(res[idx].keys())
        csvwriter = csv.DictWriter(stream,measured,restval='-----')
        csvwriter.writeheader()
        csvwriter.writerows(res)

def one_task(kind,prefix,nmin,nmax,compute):
  bench2csv(kind,TASK[kind](prefix,nmin,nmax,compute))

def all_tasks(prefix,nmin,nmax,compute):
  gen(prefix,nmin,nmax,compute)
  for kind in TASK.keys():
    print(f"Generating {kind} benchmark")
    one_task(kind,prefix,nmin,nmax,compute)
# --------------------------------------------------------------------

TASK = { 
    "theories" : theories,
    "lrs" : lrs,
    "certificates" : certificates,
    "compilation" : compilation,
    "validation" : job("Validation"),
    "diameter" : job("Diameter"),
    "hirsch" : job("Hirsch"),
    "exact" : job("Exact")
  }

ADDITIONAL = {"clean_coq" : clean_coq, "clean_data" : clean_data, "all" : all_tasks, "gen" : gen}

def optparser():
  parser = argp.ArgumentParser(
    description="Lauch the selected benchmark")

  parser.add_argument(dest="kind", help="The kind of execution required", 
                      choices=list(TASK.keys()) + list(ADDITIONAL.keys()))
  
  parser.add_argument("-p", "--prefix", dest="prefix", nargs="*", help=r"Specifies the subset on which perform the benchmarks. PREFIX is either 'hirsch' or (cube|cross|cyclic|permutahedron). Only the latter needs MIN and MAX", default=["","0","0"])
  parser.add_argument("-c", "--compute", dest="compute", help=r"vm_compute is the reduction strategy used by default, this option allows to perform using compute instead", action="store_const", const="compute", default="vm_compute")

  return parser


def main():
  args = optparser().parse_args()
  kind = args.kind
  pref = args.prefix
  compute = args.compute
  if pref[0] == "hirsch":
    prefix, nmin, nmax = "hirsch", None, None
  elif len(pref)==3:
    prefix, nmin, nmax = pref[0], int(pref[1]), int(pref[2])
  else:
    print('Error : -p option needs either "hirsch" of three parameters to work.')
    exit(1)
  if kind in TASK:
    one_task(kind,prefix,nmin,nmax,compute)
  if kind in ADDITIONAL:
    ADDITIONAL[kind](prefix,nmin,nmax,compute)

# --------------------------------------------------------------------
if __name__ == "__main__":
    main()