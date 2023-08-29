#! /usr/bin/env python3

# --------------------------------------------------------------------
import argparse as argp
import subprocess as sp
import os
import re
import time
import math
from scripts import core, lrs2dict, dict2bin, bin2coq, coqjobs, genlrs, dict2text
import csv
import shutil

CWD = os.getcwd()
TIME_MEM_PREFIX = r'TIMEFMT="%E : real time, %M : max memory" && '
HIRSCH_CEX = ["poly20dim21","poly23dim24"]
BENCH_DIR = os.path.join(os.getcwd(),"benchmarks")
DEF_GEN = {"cube" : (3,18), "cross" : (3,9), "cyclic" : (3,14), "permutohedron" : (3,9)}
PARALLEL_DFLT = 10

# --------------------------------------------------------------------

def command_call(command, prefix=""):
  output = sp.run(prefix + command,
            shell=True, executable="/bin/zsh", check=True,
            capture_output=True, text=True)
  print(output.stdout, output.stderr)
  return output.stderr

# --------------------------------------------------------------------
def format_time_output(st):
  findit = re.search(r"(?P<time>\d+)[,.](?P<mtime>\d+)s.+, (?P<memory>\d+)", st)
  time, mtime = findit.group("time"), findit.group("mtime")
  memory = findit.group("memory")
  return f"{time}.{mtime}", memory

# --------------------------------------------------------------------
def clean_coq(**kwargs):
  command_call("dune clean")

def theories(**kwargs):
  parallel = kwargs["parallel"]
  time, _ = format_time_output(command_call(f"time dune build -j {PARALLEL_DFLT if parallel is None else parallel} " + os.path.join("..","theories"),TIME_MEM_PREFIX))
  return time

# --------------------------------------------------------------------
def polytopes(**kwargs):
  datas = os.listdir(core.resource())
  prefix = kwargs["prefix"]
  if prefix == "hirsch":
    for name in datas:
      if name in ["poly20dim21", "poly23dim24"]:
        print(name)
        yield name
  elif prefix != "":
    nmin = kwargs["nmin"]
    nmax = kwargs["nmax"]
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

def lrs(**kwargs):
  res = []
  for name in polytopes(**kwargs):
    res.append({"polytope" : name})
    inefile = core.resource(name,"lrs",name+".ine")
    extfile = core.resource(name,"lrs",name+".ext")
    time, memory = format_time_output(command_call(f"time lrs {inefile} {extfile}",TIME_MEM_PREFIX))
    res[-1]["time"], res[-1]["memory"] = time, memory
  return res

# --------------------------------------------------------------------
def certificates(**kwargs):
  res = []
  compute = kwargs["compute"]
  text = kwargs["text"]
  for name in polytopes(**kwargs):
    res.append({"polytope" : name})
    hirsch = False
    if name in HIRSCH_CEX:
      hirsch = True
    st = time.time()
    dict = lrs2dict.lrs2dict(name,hirsch)
    et = time.time()
    res[-1]["time"] = f"{et - st:.2f}"
    if text:
      res2 = dict2text.dict2text(name,dict,compute)
    else:
      res2 = dict2bin.dict2bin(name,dict)
      bin2coq.main(name)
    coqjobs.main(name,"Validation",compute)
    if name in ["poly20dim21", "poly23dim24"]:
      coqjobs.main(name,"Hirsch", compute)
      coqjobs.main(name,"Exact", compute)
    else:
      coqjobs.main(name,"Diameter", compute)
    res[-1] = {**res[-1], **res2}
  return res

# --------------------------------------------------------------------
def compilation(**kwargs):
  res = []
  parallel = kwargs["parallel"]
  for name in polytopes(**kwargs):
    res.append({"polytope" : name})
    coqdir = core.resource(name,"coq")
    if parallel is None:
      times = []
      max_memory = -math.inf
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
      res[-1]["total time"] = str(math.fsum(times))
      res[-1]["max memory"] = str(max_memory)
    else:
      rel_path = os.path.join("data",name,"coq")
      st = command_call(f"time dune build -j {parallel} " + rel_path, TIME_MEM_PREFIX)
      time, memory = format_time_output(st)
      res[-1]["total time"] = time
      res[-1]["max memory"] = memory
  return res

def job(job):
  def worker(**kwargs):
    res = []
    parallel = kwargs["parallel"]
    for name in polytopes(**kwargs):
      jobdir = core.resource(name,f"coq_{job}")
      if not os.path.exists(jobdir):
        continue
      res.append({"polytope" : name})
      if parallel is None:
        times = []
        max_memory = -math.inf
        datas = list(os.listdir(jobdir))
        datas.sort(key=f"{job}.v".__eq__)
        for file in datas:
          if file.endswith(".v"):
            print(file)
            rel_path = os.path.join("data",name,f"coq_{job}",file+"o")
            st = command_call("time dune build " + rel_path,TIME_MEM_PREFIX)
            time, memory = format_time_output(st)
            res[-1][file + " time"] = time
            res[-1][file + " memory"] = memory
            times.append(float(time))
            max_memory = max(max_memory,int(memory))
        res[-1]["total time"] = str(math.fsum(times))
        res[-1]["max memory"] = str(max_memory)
      else:
        rel_path = os.path.join("data",name,f"coq_{job}")
        st = command_call(f"time dune build -j {parallel} " + rel_path, TIME_MEM_PREFIX)
        time, memory = format_time_output(st)
        res[-1]["total time"] = time
        res[-1]["max memory"] = memory
    return res
  return worker

# --------------------------------------------------------------------
def clean_data(**kwargs):
  for name in polytopes(**kwargs):
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

def clean_benchmarks(**kwargs):
  for name in os.listdir(BENCH_DIR):
    if not name.startswith("."):
      shutil.rmtree(os.path.join(BENCH_DIR, name))


# --------------------------------------------------------------------
def gen(**kwargs):
  prefix = kwargs["prefix"]
  if prefix != "":
    nmin, nmax = kwargs["nmin"], kwargs["nmax"]
    print(prefix)
    polytopes = {prefix : (nmin, nmax)}
  else:
    polytopes = DEF_GEN
  for poly, (n, N) in polytopes.items():
    for k in range(n, N+1):
      if poly == "cyclic":
        genlrs.generate_lrs(poly, k, 2*k)
      else:
        genlrs.generate_lrs(poly, k)
# --------------------------------------------------------------------
def writer(stream):
  def output(st):
    print(st,file=stream)
  return output

def sort_res(res):
  def key(elt):
    name = elt["polytope"]
    pref_match = re.search(f"([^_]+)_(\d+)", name)
    if pref_match is not None:
      return (pref_match.group(1), int(pref_match.group(2)))
    else:
      return (name,0)
  return sorted(res, key=key)


def bench2csv(kind,res,compute,text,parallel):
  taskdir = os.path.join(BENCH_DIR,kind)
  os.makedirs(taskdir,exist_ok=True)
  file_name = f"{kind}_" + (f"{compute}_" if compute == "compute" else "") + ("text_" if text else "") + (f"parallel_{parallel}_" if parallel is not None else "") + time.strftime("%m-%d-%H-%M-%S") + (".log" if kind == "theories" else ".csv")
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
        res = sort_res(res)
        csvwriter.writeheader()
        csvwriter.writerows(res)

def one_task(kind,**kwargs):
  bench2csv(kind,TASK[kind](**kwargs),kwargs["compute"],kwargs["text"],kwargs["parallel"])

def all_tasks(*args,**kwargs):
  gen(**kwargs)
  for kind in TASK.keys():
    print(f"Generating {kind} benchmark")
    one_task(kind,**kwargs)
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

ADDITIONAL = {"clean_coq" : clean_coq, "clean_data" : clean_data, "clean_benchmarks" : clean_benchmarks,  "all" : all_tasks, "gen" : gen}

def optparser():
  parser = argp.ArgumentParser(
    description="Launch the selected benchmark")

  parser.add_argument(dest="kind", help="The kind of execution required", 
                      choices=list(TASK.keys()) + list(ADDITIONAL.keys()))
  
  parser.add_argument("-p", "--prefix", dest="prefix", nargs="*", help=r"Specifies the subset on which perform the benchmarks. PREFIX is either 'hirsch' or (cube|cross|cyclic|permutohedron). Only the latter needs MIN and MAX.", default=["","0","0"])
  parser.add_argument("-c", "--compute", dest="compute", help=r"vm_compute is the reduction strategy used by default, this option allows to perform using compute instead.", action="store_const", const="compute", default="vm_compute")
  parser.add_argument("-t", "--text", dest="text", help=r"Certificates are generated as binary files by default. This option generates plain text .v files instead.", action="store_true")
  parser.add_argument("-j", "--jobs", dest="parallel", help="The compilation of Coq files by dune is done sequentially. This option calls dune on the folder instead. It is possible to add the number of task that can be simultaneously done.", nargs="?", const=PARALLEL_DFLT, default=None)

  return parser


def main():
  args = optparser().parse_args()
  kind = args.kind
  pref = args.prefix
  compute = args.compute
  text = args.text
  parallel = args.parallel
  if pref[0] == "hirsch":
    prefix, nmin, nmax = "hirsch", None, None
  elif len(pref)==3:
    prefix, nmin, nmax = pref[0], int(pref[1]), int(pref[2])
  else:
    print('Error : -p option needs either "hirsch" of three parameters to work.')
    exit(1)
  kwargs = {"prefix" : prefix, "nmin": nmin, "nmax" : nmax, "compute" : compute, "text" : text, "parallel" : parallel}
  if kind in TASK:
    one_task(kind,**kwargs)
  if kind in ADDITIONAL:
    ADDITIONAL[kind](**kwargs)

# --------------------------------------------------------------------
if __name__ == "__main__":
    main()