#!/usr/bin/env python

import os
import shutil

def get_label(segments, segment_labels):
    res = None
    for segment, label in segment_labels.items():
        if segment in segments:
            assert res is None, f"multiple {segments} {segment_labels}"
            res = label
    assert res is not None, f"none {segments} {segment_labels}"

    if isinstance(res, tuple):
        lbl, rest = res
        for x in rest:
            lbl += get_label(segments, x)
        return lbl
    else:
        assert isinstance(res, str)
        return res

rootdir = "/space/tjoa/tuning-output/v52_stlcace_w_bounds"
filename_to_dir: dict[str, str] = {}
for root, subdirs, files in os.walk(rootdir):
    if "trained_Generator.v" in files:
        assert root[:len(rootdir)] == rootdir
        segments = root[len(rootdir):].split("/")

        new = ""
        new += get_label(segments, {
            "rbt": "R_",
            "stlc": "S_",
            "bst": "B_",
        })
        new += get_label(segments, {
            "langbespoke": "Bespoke",
            "langderived": ("LD", [
                {"stack_size=2": ""},
                {
                    "intwidth=3": "Thin",
                    "intwidth=6": "",
                },
            ]),
            "langsiblingderived": ("LSD", [
                {"stack_size=2": ""},
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
                    "prop=bookkeepingANDbalanceANDorder": "",
                    "prop=order": "",
                    # todo: May, Might
                },
                {"failure_penalty=0.0": ""},
                {"forgiveness=0": ""},
                {"rand_forgiveness=true": ""},
            ]),
            "approx_entropy": "ACE",
        })
        new += get_label(segments, {
            "0.3": "LR30",
            "0.03": "LR03",
        })
        new += get_label(segments, {
            "epochs=2000": "",
        })
        new += get_label(segments, {
            "bound=0.0": "",
            "bound=0.05": "Bound05",
            "bound=0.1": "Bound10",
            "bound=0.2": "Bound20",
        })
        new += "Generator.v"

        assert new not in filename_to_dir, f"{new} {filename_to_dir}"
        filename_to_dir[new] = root

for new, root in filename_to_dir.items():
    src = os.path.join(root, "trained_Generator.v")
    dst = os.path.join(root, new)
    shutil.copyfile(src, dst)
    print(dst)
print()
for new, root in filename_to_dir.items():
    print(f"\"{new[:-2]}\",")
