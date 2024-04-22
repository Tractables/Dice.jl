#!/usr/bin/env python
import subprocess
import sys
import os
from collections import Counter, defaultdict

STRAT_DIR = "/space/tjoa/etna/workloads/Coq/RBT/Strategies/"
OUT_DIR = "/space/tjoa/Dice.jl/stats"
NUM_TESTS = 10_000

METRICS = ["size", "height"]

# Put rows in this order and also assert that all these generators exist
ORDER = [
    "BespokeGenerator.v",
    "TypeBasedGenerator.v",
    "ManualTypeBased5Generator.v",
    "CondEntropy5Generator.v",
    "OrderGenerator.v",
    "OrderIgnoreGenerator.v",
    "NoRedRed5Generator.v",
    "ManualTypeBased8Generator.v",
    "CondEntropy8Generator.v",
    "NoRedRed8Generator.v",
]
def main():
    metric_to_generator_to_counts = defaultdict(lambda: defaultdict(dict))
    for filename in ORDER:
        assert filename in os.listdir(STRAT_DIR)
    for filename in os.listdir(STRAT_DIR):
        if filename.endswith("Generator.v"):
            generator_path = os.path.join(STRAT_DIR, filename)
            print(f"Collecting stats for {filename}")
            collect_stats(generator_path, filename, metric_to_generator_to_counts)
    for metric, generator_to_counts in metric_to_generator_to_counts.items():
        max_val = max(
            n
            for counts in generator_to_counts.values()
            for n, valid in counts.keys()
        )
        min_val = min(
            n
            for counts in generator_to_counts.values()
            for n, valid in counts.keys()
        )
        assert min_val >= 0
        with open(os.path.join(OUT_DIR, f"{metric}.csv"), "w") as file:
            val_names, vals = zip(*[
                (f"{v}" if valid else f"{v}!", (v, valid))
                for v in range(0, max_val + 1)
                for valid in (True, False)
            ])
            file.write(metric + '\t' + '\t'.join(val_names) + '\n')
            for generator in [*ORDER, *[x for x in generator_to_counts if x not in ORDER]]:
                counts = generator_to_counts[generator]
                tokens = [generator]
                for val in vals:
                    tokens.append(
                        str(counts.get(val, 0) / NUM_TESTS)
                    )
                file.write('\t'.join(tokens) + "\n")

def readlines(path):
    with open(path) as f:
        return '\n'.join(f.readlines())

def lines_between(s, start, end):
    active = False
    for line in s.split('\n'):
        if line.startswith(start):
            active = True
            continue
        elif active and line.startswith(end):
            break
        elif active:
            yield line
    else:
        if active:
            raise f"Did not find {end} after {start}"
        else:
            raise f"Did not find {start}"

def collect_stats(path, filename, metric_to_generator_to_counts):
    pgrm = readlines(path)
    may_fail = filename == "BespokeGenerator.v"
    if may_fail:
        pgrm += """
    Definition collect {A : Type} `{_ : Show A}  (f : Tree -> A)  : Checker :=  
        forAll arbitrary (fun t =>    
          match t with
          | Some t =>
            if isRBT t then
                collect (append "valid " (show (f t))) true
            else
                collect (append "invalid " (show (f t))) true
          | None =>
            collect (append "failure" "") true
          end)."""
    else:
        pgrm += """
    Definition collect {A : Type} `{_ : Show A}  (f : Tree -> A)  : Checker :=  
        forAll arbitrary (fun t =>
            if isRBT t then
                collect (append "valid " (show (f t))) true
            else
                collect (append "invalid " (show (f t))) true
        ).
        """

    pgrm += f"""
    Fixpoint height (t: Tree) : nat :=
      match t with
      | E => 0
      | T c l k v r => 1 + max (height l) (height r)
      end.

    Extract Constant Test.defNumTests => "{NUM_TESTS}".

    QuickChick (collect size).
    QuickChick (collect height).
    """

    cmd = ["coqtop", "-Q", ".", "RBT"]
    os.chdir("/space/tjoa/etna/workloads/Coq/RBT")
    p = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        # stderr=sys.stderr,
        input=pgrm,
        encoding="ascii",
    )
    assert p.returncode == 0
    for metric in METRICS:
        cts = {}
        for line in lines_between(p.stdout, f"QuickChecking (collect {metric})", "+++"):
            tokens = line.split(' ')
            if "None" in tokens:
                cts["failure"] += 1
                raise NotImplementedError()
            else:
                valid = '"valid' in tokens
                invalid = '"invalid' in tokens
                assert valid ^ invalid, line
                def stripquotes(s):
                    if s.startswith('"') and s.endswith('"'):
                        return s[1:-1]
                    assert s.endswith('"')
                    return s[:-1]
                cts[int(stripquotes(tokens[-1])), valid] = int(tokens[0])
        metric_to_generator_to_counts[metric][filename] = cts

if __name__ == "__main__":
    main()
