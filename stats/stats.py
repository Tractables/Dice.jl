#!/usr/bin/env python
import subprocess
import math
import sys
import os
from datetime import datetime
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from typing import List, Callable

WORKLOAD = "RBT"
ORDER_ONLY = True
SHAPES = True
ORDER: List[str] = { # Put rows in this order and also assert that these generators exist
    "STLC": [
        # # class: bespoke
        # "BespokeGenerator",
        # "LBespokeGenerator",
        # "LBespokeACEGenerator",
        # "LBespokeApproxConstructorEntropyGenerator",
        # # class: type-based
        # "TypeBasedGenerator",
        # "LDGenerator",
        # "LDEqMightGenerator",
        # "LDEqVarGenerator",
        # "LDEqWellGenerator",
        # "LDStructureMightGenerator",
        # "LDStructureVarGenerator",
        # "LDStructureWellGenerator",
        # "LSDGenerator",
        # "LSDStructureMightGenerator",
        # "LSDStructureWellGenerator",
        # "LSDGenerator",
        # "LSDStructureMayGenerator",
        # "LSDEqMayGenerator",
        # "LDStructureMayGenerator",
        # "LDEqMayGenerator",
        # "LDMayStructureArb_Freq5_SPB50_LR10Generator",
        # "LDMayStructureArb_Freq5_SPB50_LR30Generator",
        # "LDMayStructureArb_Freq5_SPB50_LR50Generator",
        # "TBMay10Generator",
        # "TBMay30Generator",
        # "TBMay50Generator",
        # "ReproTBMightGenerator",
# "LDMayStructureArb_Freq2_SPB200_LR10Generator",
# "LDMayStructureArb_Freq2_SPB200_LR30Generator",
# "LDMayStructureArb_Freq2_SPB200_LR50Generator",
# "LDMayStructureArb_Freq2_SPB50_LR10Generator",
# "LDMayStructureArb_Freq2_SPB50_LR30Generator",
# "LDMayStructureArb_Freq2_SPB50_LR50Generator",
# "LDMayStructureArb_Freq5_SPB200_LR10Generator",
        "LDThinInitGenerator",
        # "LDThinMayEqGenerator",
        # "LDThinMayStructureGenerator",
        # "LDThinMayStructureGenerator",
        # "LDThinMayStructure2Generator",
    ] + [
        f"{template}May{eq}Bound{bound}Generator"
        for template in ["LD", "LSD"]
        for eq in ["Structure", "Eq"]
        for bound in ["05", "10"]
    ],

    "RBT": [
        # "SpecGenerator",
        "RLSDThinSmallGenerator",
        "SpecBoundGenerator",
        "RLSDThinEqLR30Epochs2000Bound10SPB200Generator",
        "RLSDThinEqValidLR30Epochs2000Bound10SPB200Generator",

        # "TypeBasedGenerator",
        # "LSDEqGenerator",
        # "LSDExceptNumsGenerator",
        # "LSDEq2Generator",
        # "LSDExcept2Generator",
        # "LSDGenerator",
    ],

    "BST": [
        "TypeBasedGenerator",
        "LEqGenerator",
        "LExceptGenerator",
        "TBEqGenerator",
        "TBExceptGenerator",
    ]
}[WORKLOAD]

STRAT_DIR = f"/scratch/tjoa/etna/workloads/Coq/{WORKLOAD}/Strategies/"
OUT_DIR = f"/scratch/tjoa/Dice.jl/stats/{WORKLOAD}"
COQ_PROJECT_DIR = f"/scratch/tjoa/etna/workloads/Coq/{WORKLOAD}"
NUM_TESTS = 100000

@dataclass
class Workload:
    type: str
    generator: Callable[[str],str]
    invariant_check: str
    metrics: List[str]
    extra_definitions: str
    is_failing_generator: Callable[[str],bool]
    unique_extra: str

WORKLOADS = {
    "STLC": Workload(
        type="Expr",
        generator=lambda _:"gSized",
        invariant_check="isJust (mt %s)",
        metrics=["sizeSTLC", "num_apps"],
        extra_definitions="""
            Fixpoint num_apps (e: Expr) : nat :=
                match e with
                | (Abs _ e) => num_apps e
                | (App e1 e2) => 1 + num_apps e1 + num_apps e2
                | _ => 0
                end.""",
        is_failing_generator=lambda generator: "Bespoke" in generator,
        unique_extra="""Inductive Shape :=
| E_ : Shape
| T_ : Color -> Shape -> Shape -> Shape.

Fixpoint toShape (t : Tree) : Shape := match t with
  | E => E_
  | T c l k v r => T_ c (toShape l) (toShape r)
  end.""",
    ),

    "BST": Workload(
        type="Tree",
        generator=lambda _:"gSized",
        invariant_check="isBST %s",
        metrics=["size", "height"],
        extra_definitions="""
            Fixpoint height (t: Tree) : nat :=
              match t with
              | E => 0
              | T l k v r => 1 + max (height l) (height r)
              end.""",
        is_failing_generator=lambda generator: False,
        unique_extra="",
    ),
    "RBT": Workload(
        type="Tree",
        generator=lambda generator: "arbitrary" if "typebased" in generator.lower() else "gSized",
        invariant_check="isRBT %s",
        metrics=["size", "height"],
        extra_definitions="""
            Fixpoint height (t: Tree) : nat :=
              match t with
              | E => 0
              | T c l k v r => 1 + max (height l) (height r)
              end.""",
        is_failing_generator=lambda generator: generator == "BespokeGenerator.v",
        unique_extra="""Inductive Shape :=
| E_ : Shape
| T_ : Color -> Shape -> Shape -> Shape.

Fixpoint toShape (t : Tree) : Shape := match t with
  | E => E_
  | T c l k v r => T_ c (toShape l) (toShape r)
  end.""",
    ),
}


workload = WORKLOADS[WORKLOAD]

ORDER = [
    f"{s}.v"
    for s in ORDER
]

def get_generators():
    generators = [
        generator
        for generator in os.listdir(STRAT_DIR)
        if generator.endswith("Generator.v")
        and not (ORDER_ONLY and generator not in ORDER)
    ]
    for generator in ORDER:
        assert generator in generators, generator
    def key(generator):
        if generator in ORDER:
            return ORDER.index(generator)
        else:
            return math.inf
    generators.sort(key=key)
    return generators

def collect_unique_shapes():
    # List generators
    generators = get_generators()
    cols = []
    for generator in get_generators():
        path = os.path.join(STRAT_DIR, generator)
        print(f"Unique over time for {generator}")
        pgrm = read(path) 
        pgrm += workload.unique_extra
        samples = []

        # to get an idea overhead per run:
        # 100k samples, limit 1000 took 141 seconds
        # 100k samples, limit 10,000 took 14 seconds
        limit = 2000 if generator == "RLSDThinEqLR30Epochs2000Bound10SPB200Generator.v" else 10000
        print(limit)
        while len(samples) < NUM_TESTS:
            n_now = min(limit, NUM_TESTS - len(samples))
            stdout=run_coq(pgrm + f"""
            Derive Show for Shape.

            Extract Constant Test.defNumTests => "1".
            Definition collect {{A : Type}} `{{_ : Show A}} (g : G A)   : Checker :=  
                forAll g (fun (t : A) =>
                      collect (show t) true
                ).

            Set Warnings "-abstract-large-number".
            Definition numSamples := {n_now}.

            Definition gShapes :=
              bindGen (vectorOf numSamples (bindGen {workload.generator(generator)} (fun t => returnGen
                (if """ + (workload.invariant_check % "t") + """ then
                    Some (toShape t)
                else
                    None)
              ))) (fun samples =>
                returnGen samples).

            QuickChick (collect gShapes).
            """)
            line, = lines_between(stdout, f"QuickChecking (collect gShapes)", "+++")
            samples.extend(line.replace("1 : \"[","").replace("]\"", "").split("; "))

        seen = set()
        col = [generator]
        for sample in samples:
            if sample != "None":
                assert sample.startswith("Some")
                seen.add(sample)
            col.append(str(len(seen)))
        cols.append(col)

    # Output stats
    os.makedirs(OUT_DIR, exist_ok=True)
    file_path = os.path.join(OUT_DIR, f"shapes-{WORKLOAD}.csv")
    rows = list(map(list, zip(*cols, strict=True)))
    with open(file_path, "w") as file:
        for row in rows:
            file.write("\t".join(row) + "\n")
        print(f"Write to {file_path}")

def collect_dist():
    # Collect stats
    metric_to_generator_to_counts = defaultdict(lambda: defaultdict(dict))
    for generator in generators:
        path = os.path.join(STRAT_DIR, generator)
        print(f"Collecting stats for {generator}")
        collect_stats(path, generator, metric_to_generator_to_counts)

    # Output stats
    os.makedirs(OUT_DIR, exist_ok=True)
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
        file_path = os.path.join(OUT_DIR, f"{metric}.csv")
        with open(file_path, "w") as file:
            val_names, vals = zip(*[
                (f"{v}" if valid else f"{v}!", (v, valid))
                for v in range(0, max_val + 1)
                for valid in (True, False)
            ])
            file.write(metric + '\t' + '\t'.join(val_names) + '\n')
            for generator in generators:
                counts = generator_to_counts[generator]
                tokens = [generator]
                for val in vals:
                    tokens.append(
                        str(counts.get(val, 0) / NUM_TESTS)
                    )
                file.write('\t'.join(tokens) + "\n")
        print(f"Write to {file_path}")

def main():
    if SHAPES:
        collect_unique_shapes()
    else:
        collect_dist()

def read(path):
    with open(path) as f:
        return f.read()

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

def run_coq(pgrm):
    os.chdir(COQ_PROJECT_DIR)
    cmd = ["coqtop", "-Q", ".", WORKLOAD]
    p = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        input=pgrm,
        encoding="ascii",
    )

    # Check for errors
    def remove_junk(s):
        return s.replace("Coq < ","").replace("dec_type < ","")
    if any(
        remove_junk(s).strip()
        for s in p.stderr.split('\n')
    ):
        now = datetime.now().strftime("%Y_%m_%d__%H_%M_%S")
        pgrm_dump = f"/tmp/program{now}.v"
        with open(pgrm_dump, "w") as file:
            file.write(pgrm)
        print(f"Wrote program to {pgrm_dump}")

        print("STDERR =====")
        last_line_blank = False
        for s in p.stderr.split('\n'):
            s = remove_junk(s)
            # no double newlines
            line_blank = len(s.strip()) == 0
            if not (line_blank and last_line_blank):
                print(s)
            last_line_blank = line_blank

        exit(1)
    assert p.returncode == 0
    return p.stdout

def collect_stats(path, generator, metric_to_generator_to_counts):
    pgrm = read(path)
    pgrm += workload.extra_definitions
    may_fail = workload.is_failing_generator(generator)
    if may_fail:
        pgrm += """
    Definition collect {A : Type} `{_ : Show A}  (f : """ + workload.type + """ -> A)  : Checker :=  
        forAll """ + workload.generator(generator) + """ (fun (t : option """ + workload.type + """) =>
          match t with
          | Some t =>
            if """ + (workload.invariant_check % "t") + """ then
                collect (append "valid " (show (f t))) true
            else
                collect (append "invalid " (show (f t))) true
          | None =>
            collect (append "failure" "") true
          end)."""
    else:
        pgrm += """
    Definition collect {A : Type} `{_ : Show A} (f : """ + workload.type + """  -> A)  : Checker :=  
        forAll """ + workload.generator(generator) + """ (fun (t : """ + workload.type + """) =>
            if """ + (workload.invariant_check % "t") + """ then
                collect (append "valid " (show (f t))) true
            else
                collect (append "invalid " (show (f t))) true
        ).
        """

    pgrm += f"""\nExtract Constant Test.defNumTests => "{NUM_TESTS}".\n"""
    for metric in workload.metrics:
        pgrm += f"QuickChick (collect {metric}).\n"

    stdout = run_coq(pgrm)
    for metric in workload.metrics:
        cts = {}
        for line in lines_between(stdout, f"QuickChecking (collect {metric})", "+++"):
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
        metric_to_generator_to_counts[metric][generator] = cts

if __name__ == "__main__":
    main()
