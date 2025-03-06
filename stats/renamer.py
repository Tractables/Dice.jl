#!/usr/bin/env python
rootdir = "/space/tjoa/tuning-output/v56_rbt_thin"
# rootdir = "/space/tjoa/tuning-output/v55_stlc_faster"

rootdir = "/space2/tjoa/tuning-output/v66_fig2_rbt"
rootdir = "/space2/tjoa/tuning-output/v69_attempt_stlctb_faster"

rootdir = "/scratch/tjoa/tuning-output/v114_rbt_table"
rootdir = "/space2/tjoa/tuning-output/v119_4321"
rootdir = "/space2/tjoa/tuning-output/v120_stlctbeval"

import os
import shutil

def get_label(segments, segment_labels):
    res = None
    for segment, label in segment_labels.items():
        if segment in segments:
            assert res is None, f"multiple {segments} {segment_labels}"
            res = label
    assert res is not None, f"none {segments} {segment_labels.keys()}"

    if isinstance(res, tuple):
        lbl, rest = res
        for x in rest:
            lbl += get_label(segments, x)
        return lbl
    else:
        assert isinstance(res, str)
        return res

filename_to_dir: dict[str, str] = {}
for root, subdirs, files in os.walk(rootdir):
    if "trained_Generator.v" in files:
        assert root[:len(rootdir)] == rootdir
        print(root)
        segments = root[len(rootdir):].split("/")

        new = ""
        new += get_label(segments, {
            "rbt": "R",
            "stlc": "S",
            "bst": "B",
        })
        new += get_label(segments, {
            "langbespoke": "Bespoke",
            "langderived": ("LD", [
                {
                    "stack_size=2": "",
                },
                {
                    "intwidth=3": "Thin",
                    "intwidth=6": "",
                },
            ]),
            "langsiblingderived": ("LSD", [
                {
                    "stack_size=2": "",
                    "stack_size=1": "Stack1",
                },
                {
                    "intwidth=3": "Thin",
                    "intwidth=6": "",
                },
            ]),
        })
        new += get_label(segments, {
            "reinforce_sampling_entropy": ("", [
                {
                    "eq=eq_except_numbers": "Except",
                    "eq=eq_structure": "Structure",
                    "eq=prob_equals": "Eq",
                },
                {
                    "prop=bookkeepingANDbalanceANDorder": "Valid",
                    "prop=order": "",
                    "prop=stlcwelltyped": "Well",
                    "prop=trueproperty": "",
                    # todo: May, Might
                },
                {"failure_penalty=0.0": ""},
                {"forgiveness=0": ""},
                {"rand_forgiveness=true": ""},
            ]),
            "approx_entropy": "ACE",
            "spec_entropy": ("SE", [
                {
                    "freq=5-spb=200": "Freq5SPB200",
                    "freq=5-spb=100": "Freq5SPB100",
                    "freq=5-spb=50": "Freq5SPB50",
                    "freq=2-spb=200": "Freq2SPB200",
                    "freq=2-spb=100": "Freq2SPB100",
                    "freq=2-spb=50": "Freq2SPB50",
                    "freq=1-spb=200": "Freq1SPB200",
                    "freq=1-spb=100": "Freq1SPB100",
                    "freq=1-spb=50": "Freq1SPB50",
                },
                {
                    "prop=always_true": "AlwaysTrue",
                    "prop=isRBT": "IsRBT",
                    "prop=wellTyped": "WellTyped",
                    "prop=isBST": "IsBST",
                },
            ]),
            "satisfy_property": ("Prop", [
                {
                    "prop=always_true": "AlwaysTrue",
                    "prop=isRBTdist": "IsRBT",
                },
            ]),
            "mle" : ("MLE", [
                {
                    "num_apps": "NumApps",
                },
                {
                    "target4321": "Target4321",
                    "target333": "Target333",
                }

            ]),
        })
        new += get_label(segments, {
            "1.0": "LR1",
            "0.3": "LR30",
            "0.1": "LR10",
            "0.03": "LR03",
            "0.01": "LR01",
        })
        # new += get_label(segments, {
        #     "ty-sizes=Main.ColorKVTree.t-6-Main.Color.t-0": "Sz6",
        #     "ty-sizes=Main.ColorKVTree.t-8-Main.Color.t-0": "Sz8",
        # })
        new += get_label(segments, {
            "epochs=1000": "Epochs1000",
            "epochs=2000": "Epochs2000",
            "epochs=700": "Epochs700",
            "epochs=500": "Epochs500",
            "epochs=250": "Epochs250",
        })
        new += get_label(segments, {
            "bound=0.0": "",
            "bound=0.05": "Bound05",
            "bound=0.1": "Bound10",
            "bound=0.2": "Bound20",
        })
        new += "Generator.v"

        assert new not in filename_to_dir, f"{new}\n{root}\n{filename_to_dir[new]}"
        filename_to_dir[new] = root

for new, root in filename_to_dir.items():
    src = os.path.join(root, "trained_Generator.v")
    dst = os.path.join(root, new)
    shutil.copyfile(src, dst)
    print(dst)
print()
for new, root in filename_to_dir.items():
    print(f"\"{new[:-2]}\",")
