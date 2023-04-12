EXPERIMENTS_DIR = "experiments/dicejl"
OUTPUT_DIR = "bddsizes"
EXPERIMENTS = [
    ("book", "book_mod.jl"),
    ("tugofwar", "tugofwar.jl"),
    ("caesar-small", "caesar_small.jl"),
    ("caesar-medium", "caesar_medium.jl"),
    ("caesar-large", "caesar_large.jl"),
    ("caesar-huge", "caesar_huge.jl"),
    ("ranking-small", "ranking_small.jl"),
    ("ranking-medium", "ranking_medium.jl"),
    ("ranking-large", "ranking_large.jl"),
    ("radar1", "radar.jl"),
    ("floydwarshall-small", "fw_small.jl"),
    ("floydwarshall-medium", "fw_medium.jl"),
    ("floydwarshall-large", "fw_large.jl"),
    ("linear extensions-small", "linext_small.jl"),
    ("linear extensions-medium", "linext_medium.jl"),
    ("linear extensions-large", "linext_large.jl"),
    ("triangle-mod-small", "triangle_small.jl"),
    ("triangle-mod-medium", "triangle_medium.jl"),
    ("triangle-mod-large", "triangle_large.jl"),
    ("gcd-small", ""),
    ("gcd-medium", ""),
    ("gcd-large", ""),
    ("disease-large", "disease_large.jl"),
    ("disease-medium", "disease_medium.jl"),
    ("disease-small", "disease_small.jl"),
    ("luhn-small", "luhn_small.jl"),
    ("luhn-medium", "luhn_medium.jl"),
]

########

import os
import sys
import subprocess
from datetime import datetime
import time



if not os.path.isdir(OUTPUT_DIR):
    os.mkdir(OUTPUT_DIR)
   

timestamp = datetime.now().strftime("%Y-%m-%d_%Hh%Mm%Ss")

output_path = os.path.join(OUTPUT_DIR, f"{timestamp} bdd sizes")

def flprint(*args, **kwargs):
    print(*args, flush=True, **kwargs)


def get_path_bdd_size(path):
    if not os.path.isfile(path):
        flprint("Missing!")
        return None
    try:
        completed = subprocess.run(
            ["julia", "--project", path],
            stdout=subprocess.PIPE,
            # stderr=subprocess.PIPE,
            # timeout=3000,
        )
        if completed.returncode == 137:
            flprint("Out of memory; got return code 137. Treating as timeout")
            return None
        if completed.returncode != 0:
            flprint(f"Non-zero return code {completed.returncode}")
            return None
        
        lastlast, last, res = None, None, None
        flprint(f"stdout: {completed.stdout}")
        flprint(f"stderr: {completed.stderr}")
        for line in completed.stdout.decode().split('\n'):
            if line == "NUM_NODES_END":
                assert lastlast == "NUM_NODES_START"
                assert res is None
                res = last
            lastlast, last = last, line
        assert res is not None
        return res

    except subprocess.TimeoutExpired:
        flprint(f"Timed out!")
        return None

table = []
for name, fname in EXPERIMENTS:
    flprint("Starting", name, fname, "===========")
    path = os.path.join(EXPERIMENTS_DIR, fname)
    tic = time.monotonic()
    bdd_size = get_path_bdd_size(path)
    toc = time.monotonic()
    flprint(f"Took {toc - tic}")
    if bdd_size is None:
        table.append((name, ''))
    else:
        table.append((name, bdd_size))
    flprint()

    with open(output_path, "a") as output_file:
        output_file.write('\t'.join(table[-1]) + "\n")
