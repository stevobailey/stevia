
# converts a filelist to arguments for tools
# currently just passes design files for lint

import os
import sys

files = []

def proc_file(filename):
    filename = os.path.expandvars(filename)
    files.append(filename)

def proc_filelist(filename):
    filename = os.path.expandvars(filename)
    with open(filename) as fl:
        for line in fl:
            line = line.strip()
            if not line or line.startswith("//") or line.startswith("#") or line.startswith("+incdir+"):
                continue
            if line.startswith("-f") or line.startswith("-F"):
                proc_filelist(line.split()[1])
            else:
                proc_file(line)

for fl in sys.argv[1:]:
    proc_filelist(fl)

for file in files:
    print(file)
