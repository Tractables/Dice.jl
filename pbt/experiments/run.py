#!/usr/bin/env python3
"""
Script to run experiments and generate distribution plots.

This script runs experiments with different configurations and generates bar charts
comparing initial, trained, and target distributions. It supports:

1. Multiple experiment types:
   - RBT Type-Based (Uniform/Linear)
   - STLC Type-Based (Uniform/Linear)
   - STLC Bespoke (Uniform/Linear)

2. Command line arguments:
   --verbose: Print detailed file paths
   --parallel: Run experiments in parallel
   --epochs: Number of epochs to run (default: 100)
   --learning-rate: Learning rate to use (default: 0.3)

For each experiment:
1. Runs the Julia command
2. Parses the log file path from stdout
3. Extracts paths to initial and trained distribution files
4. Reads the distribution files (CSV format with val,probability columns)
5. Generates a bar chart comparing:
   - Initial distribution (red)
   - Trained distribution (blue)
   - Target distribution (white with black hatching)
6. Saves the plot to experiments-output directory

Example command output:
Logging to /path/to/tuning-output/v122_more_ablation/rbt/langderived/root_ty=Main.ColorKVTree.t/ty-sizes=Main.ColorKVTree.t-4-Main.Color.t-0/stack_size=0/intwidth=3/arbitrary_prims=true/mle/depth/uniform/0.1/epochs=1000/bound=0.0/log.log

Example log file contents:
Saved metric dist to /path/to/tuning-output/v122_more_ablation/rbt/langderived/root_ty=Main.ColorKVTree.t/ty-sizes=Main.ColorKVTree.t-4-Main.Color.t-0/stack_size=0/intwidth=3/arbitrary_prims=true/mle/depth/uniform/0.1/epochs=1000/bound=0.0/loss1_dist_depth_initial.csv
Saved metric dist to /path/to/tuning-output/v122_more_ablation/rbt/langderived/root_ty=Main.ColorKVTree.t/ty-sizes=Main.ColorKVTree.t-4-Main.Color.t-0/stack_size=0/intwidth=3/arbitrary_prims=true/mle/depth/uniform/0.1/epochs=1000/bound=0.0/loss1_dist_depth_trained.csv
"""

import subprocess
import re
import pandas as pd
import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend
import matplotlib.pyplot as plt
import os
import sys
import argparse
import multiprocessing
from functools import partial
import glob
import shutil

def run_experiment(command):
    """Run the Julia command and return the log file path from stdout."""
    result = subprocess.run(command, capture_output=True, text=True)
    if result.returncode != 0:
        print("Error: Command failed with status", result.returncode)
        print("stderr:", result.stderr)
        sys.exit(1)
    
    # Extract log file path from stdout
    log_match = re.search(r'Logging to (.*?)\n', result.stdout)
    if not log_match:
        print("Error: Could not find log file path in output")
        print("stdout:", result.stdout)
        sys.exit(1)
    
    return log_match.group(1)

def parse_dist_paths(log_path):
    """Parse initial and trained distribution paths from the log file."""
    with open(log_path, 'r') as f:
        log_content = f.read()
    
    # Find paths to distribution files
    initial_match = re.search(r'Saved metric dist to (.*?loss1_dist_depth_initial\.csv)', log_content)
    trained_match = re.search(r'Saved metric dist to (.*?loss1_dist_depth_trained\.csv)', log_content)
    
    if not initial_match or not trained_match:
        print("Error: Could not find distribution file paths in log")
        sys.exit(1)
    
    return initial_match.group(1), trained_match.group(1)

def read_distribution(file_path):
    """Read a distribution file and return a pandas DataFrame."""
    return pd.read_csv(file_path, sep='\t')

def get_target_distribution(initial_dist, target_type='uniform'):
    """Calculate target distribution based on type."""
    max_val = max(initial_dist['val'])
    if target_type == 'uniform':
        target_prob = 1.0 / (max_val + 1)
        probs = [target_prob] * len(initial_dist)
    else:  # linear
        # Linear increasing from 0
        probs = [val for val in initial_dist['val']]
        # Normalize to sum to 1
        total = sum(probs)
        probs = [p/total for p in probs]
    
    return pd.DataFrame({
        'val': initial_dist['val'],
        'probability': probs
    })

def plot_distributions(initial_dist, trained_dist, output_path, target_type='uniform', exp_name=''):
    """Plot initial and trained distributions as a bar chart."""
    plt.figure(figsize=(10, 6))
    
    # Plot bars with LaTeX-like colors
    x = initial_dist['val']
    width = 0.25  # Made slightly smaller to accommodate three bars
    
    # Colors matching LaTeX definitions:
    # \trainedcolor{blue!70!cyan} -> Matplotlib-like blue
    # \initialcolor{red!80!white} -> Less harsh red
    trained_color = '#1E88E5'  # A blue that's close to blue!70!cyan
    initial_color = '#FF3333'  # A softer red that's close to red!80!white
    
    # Calculate target distribution
    target_dist = get_target_distribution(initial_dist, target_type)
    
    plt.bar(x - width, initial_dist['probability'], width, label='Initial', alpha=0.7, color=initial_color)
    plt.bar(x, trained_dist['probability'], width, label='Trained', alpha=0.7, color=trained_color)
    plt.bar(x + width, target_dist['probability'], width, label='Target', 
            color='white', edgecolor='black', hatch='///', alpha=0.7)
    
    plt.xlabel('Value')
    plt.ylabel('Probability')
    
    # Format title from experiment name
    title = exp_name.replace('_', ' ').title()
    title = title.replace('Rbt', 'RBT').replace('Stlc', 'STLC')
    plt.title(f'{title} ({target_type.capitalize()})')
    
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    # Save plot
    plt.savefig(output_path)
    plt.close()

def run_single_experiment(exp_config, verbose=False):
    """Run a single experiment and generate its plots."""
    # Run experiment and get log path
    log_path = run_experiment(exp_config['command'])
    if verbose:
        print(f"Log file: {log_path}")
    
    # Parse distribution paths
    initial_path, trained_path = parse_dist_paths(log_path)
    if verbose:
        print(f"Initial dist: {initial_path}")
        print(f"Trained dist: {trained_path}")
    
    # Read distributions
    initial_dist = read_distribution(initial_path)
    trained_dist = read_distribution(trained_path)
    
    # Verify val columns match
    if not initial_dist['val'].equals(trained_dist['val']):
        print("Error: Value columns do not match between initial and trained distributions")
        sys.exit(1)
    
    # Create experiments-output directory if it doesn't exist
    output_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(__file__))), 'experiments-output')
    os.makedirs(output_dir, exist_ok=True)
    
    # Generate plot
    plot_path = os.path.join(output_dir, f"fig2_{exp_config['name']}.png")
    plot_distributions(initial_dist, trained_dist, plot_path, exp_config['target_type'], exp_config['name'])
    print(f"Plot saved to: {plot_path}")

def run_experiments_parallel(experiments, verbose=False):
    """Run experiments in parallel using multiprocessing."""
    # Create a pool of workers
    num_workers = min(len(experiments), multiprocessing.cpu_count())
    pool = multiprocessing.Pool(processes=num_workers)
    
    # Create a partial function with the verbose parameter
    run_exp = partial(run_single_experiment, verbose=verbose)
    
    # Run experiments in parallel
    pool.map(run_exp, experiments)
    pool.close()
    pool.join()

def main():
    parser = argparse.ArgumentParser(description='Run experiments and generate distribution plots')
    parser.add_argument('--verbose', action='store_true', help='Print detailed file paths')
    parser.add_argument('--parallel', action='store_true', help='Run experiments in parallel')
    parser.add_argument('--figure', type=int, choices=[2, 3], help='Which figure to generate (2 or 3). If not specified, generates all figures.')
    parser.add_argument('--fig2-learning-rate', type=float, default=0.3, help='Learning rate for figure 2 experiments (default: 0.3)')
    parser.add_argument('--fig2-epochs', type=int, default=100, help='Number of epochs for figure 2 experiments (default: 100)')
    parser.add_argument('--fig3-learning-rate', type=float, default=0.3, help='Learning rate for figure 3 experiment (default: 0.3)')
    parser.add_argument('--fig3-epochs', type=int, default=2000, help='Number of epochs for figure 3 experiment (default: 2000)')
    args = parser.parse_args()
    
    # Define all experiments for figure 2
    figure2_experiments = [
        # RBT Type-Based Uniform
        {
            'name': 'rbt_type_based_uniform',
            'target_type': 'uniform',
            'command': [
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangDerivedGenerator{RBT}(Main.ColorKVTree.t,Pair{Type,Integer}[Main.ColorKVTree.t=>4,Main.Color.t=>0],0,3,true)",
                f"Pair{{MLELossConfig{{RBT}},Float64}}[MLELossConfig{{RBT}}(depth,Uniform())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        },
        # RBT Type-Based Linear
        {
            'name': 'rbt_type_based_linear',
            'target_type': 'linear',
            'command': [
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangDerivedGenerator{RBT}(Main.ColorKVTree.t,Pair{Type,Integer}[Main.ColorKVTree.t=>4,Main.Color.t=>0],0,3,true)",
                f"Pair{{MLELossConfig{{RBT}},Float64}}[MLELossConfig{{RBT}}(depth,Linear())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        },
        # STLC Type-Based Uniform
        {
            'name': 'stlc_type_based_uniform',
            'target_type': 'uniform',
            'command': [
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangDerivedGenerator{STLC}(Main.Expr.t,Pair{Type,Integer}[Main.Expr.t=>5,Main.Typ.t=>2],0,3,true)",
                f"Pair{{MLELossConfig{{STLC}},Float64}}[MLELossConfig{{STLC}}(depth,Uniform())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        },
        # STLC Type-Based Linear
        {
            'name': 'stlc_type_based_linear',
            'target_type': 'linear',
            'command': [
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangDerivedGenerator{STLC}(Main.Expr.t,Pair{Type,Integer}[Main.Expr.t=>5,Main.Typ.t=>2],0,3,true)",
                f"Pair{{MLELossConfig{{STLC}},Float64}}[MLELossConfig{{STLC}}(depth,Linear())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        },
        # STLC Bespoke Uniform
        {
            'name': 'stlc_bespoke_uniform',
            'target_type': 'uniform',
            'command': [
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangBespokeSTLCGenerator(5,2)",
                f"Pair{{MLELossConfig{{STLC}},Float64}}[MLELossConfig{{STLC}}(depth,Uniform())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        },
        # STLC Bespoke Linear
        {
            'name': 'stlc_bespoke_linear',
            'target_type': 'linear',
            'command': [
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangBespokeSTLCGenerator(5,2)",
                f"Pair{{MLELossConfig{{STLC}},Float64}}[MLELossConfig{{STLC}}(depth,Linear())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        }
    ]

    # Define experiment for figure 3
    figure3_experiment = {
        'name': 'stlc_unique_types',
        'command': [
            "julia", "--project", "pbt/experiments/tool.jl",
            "-f",
            "LangSiblingDerivedGenerator{STLC}(Main.Expr.t,Pair{Type,Integer}[Main.Expr.t=>5,Main.Typ.t=>2],2,3)",
            f"Pair{{FeatureSpecEntropy{{STLC}},Float64}}[FeatureSpecEntropy{{STLC}}(1,{args.fig3_epochs},wellTyped,typecheck_ft,true)=>{args.fig3_learning_rate}]",
            str(args.fig3_epochs),
            "0.0"
        ]
    }

    def run_figure2():
        if args.parallel:
            print(f"Running {len(figure2_experiments)} experiments for figure 2 in parallel...")
            run_experiments_parallel(figure2_experiments, args.verbose)
        else:
            for exp in figure2_experiments:
                print(f"\nRunning {exp['name']} experiment...")
                run_single_experiment(exp, args.verbose)

    def run_figure3():
        print("\nRunning experiment for figure 3...")
        # Run experiment and get log path
        log_path = run_experiment(figure3_experiment['command'])
        if args.verbose:
            print(f"Log file: {log_path}")
        
        # Get the directory containing the log file
        log_dir = os.path.dirname(log_path)
        
        # Create experiments-output directory if it doesn't exist
        output_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(__file__))), 'experiments-output')
        os.makedirs(output_dir, exist_ok=True)
        
        # Copy feature distribution plot
        feature_dist_pattern = os.path.join(log_dir, 'feature_dist.*.png')
        feature_dist_files = glob.glob(feature_dist_pattern)
        if not feature_dist_files:
            print("Error: Could not find feature distribution plot")
            sys.exit(1)
        shutil.copy2(feature_dist_files[0], os.path.join(output_dir, 'fig3a_stlc_unique_types_dist.png'))
        print(f"Copied feature distribution plot to: fig3a_stlc_unique_types_dist.png")
        
        # Copy unique curves plot
        unique_curves_pattern = os.path.join(log_dir, 'unique_curves.*.svg')
        unique_curves_files = glob.glob(unique_curves_pattern)
        if not unique_curves_files:
            print("Error: Could not find unique curves plot")
            sys.exit(1)
        shutil.copy2(unique_curves_files[0], os.path.join(output_dir, 'fig3b_stlc_cumulative_unique_types.svg'))
        print(f"Copied unique curves plot to: fig3b_stlc_cumulative_unique_types.svg")

    # Run the requested figures
    if args.figure is None:
        # Run all figures
        run_figure2()
        run_figure3()
    elif args.figure == 2:
        run_figure2()
    else:  # figure == 3
        run_figure3()

if __name__ == "__main__":
    main()

