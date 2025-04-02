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
   --all: Run all figures
   --fig2: Run figure 2 experiments
   --fig3: Run figure 3 experiment
   --fast: Use faster training settings
   --fig2-learning-rate: Learning rate for figure 2
   --fig2-epochs: Epochs for figure 2
   --fig3-learning-rate: Learning rate for figure 3
   --fig3-epochs: Epochs for figure 3
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
from typing import List, Dict, Any, Optional
from dataclasses import dataclass

@dataclass
class Experiment:
    """Represents a single experiment configuration."""
    name: str
    command: List[str]
    target_type: Optional[str] = None

class ExperimentRunner:
    """Handles running experiments and managing their output."""
    
    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.output_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(__file__))), 'experiments-output')
        os.makedirs(self.output_dir, exist_ok=True)
    
    def run_experiment(self, command: List[str]) -> str:
        """Run a Julia command and return the log file path."""
        result = subprocess.run(command, capture_output=True, text=True)
        if result.returncode != 0:
            print("Error: Command failed with status", result.returncode)
            print("stderr:", result.stderr)
            sys.exit(1)
        
        log_match = re.search(r'Logging to (.*?)\n', result.stdout)
        if not log_match:
            print("Error: Could not find log file path in output")
            print("stdout:", result.stdout)
            sys.exit(1)
        
        return log_match.group(1)
    
    def parse_dist_paths(self, log_path: str) -> tuple[str, str]:
        """Parse initial and trained distribution paths from the log file."""
        with open(log_path, 'r') as f:
            log_content = f.read()
        
        initial_match = re.search(r'Saved metric dist to (.*?loss1_dist_depth_initial\.csv)', log_content)
        trained_match = re.search(r'Saved metric dist to (.*?loss1_dist_depth_trained\.csv)', log_content)
        
        if not initial_match or not trained_match:
            print("Error: Could not find distribution file paths in log")
            sys.exit(1)
        
        return initial_match.group(1), trained_match.group(1)
    
    def read_distribution(self, file_path: str) -> pd.DataFrame:
        """Read a distribution file and return a pandas DataFrame."""
        return pd.read_csv(file_path, sep='\t')
    
    def get_target_distribution(self, initial_dist: pd.DataFrame, target_type: str = 'uniform') -> pd.DataFrame:
        """Calculate target distribution based on type."""
        max_val = max(initial_dist['val'])
        if target_type == 'uniform':
            target_prob = 1.0 / (max_val + 1)
            probs = [target_prob] * len(initial_dist)
        else:  # linear
            probs = [val for val in initial_dist['val']]
            total = sum(probs)
            probs = [p/total for p in probs]
        
        return pd.DataFrame({
            'val': initial_dist['val'],
            'probability': probs
        })
    
    def plot_distributions(self, initial_dist: pd.DataFrame, trained_dist: pd.DataFrame, 
                         output_path: str, target_type: str = 'uniform', exp_name: str = '') -> None:
        """Plot initial and trained distributions as a bar chart."""
        plt.figure(figsize=(10, 6))
        
        x = initial_dist['val']
        width = 0.25
        
        trained_color = '#1E88E5'  # blue!70!cyan
        initial_color = '#FF3333'  # red!80!white
        
        target_dist = self.get_target_distribution(initial_dist, target_type)
        
        plt.bar(x - width, initial_dist['probability'], width, label='Initial', alpha=0.7, color=initial_color)
        plt.bar(x, trained_dist['probability'], width, label='Trained', alpha=0.7, color=trained_color)
        plt.bar(x + width, target_dist['probability'], width, label='Target', 
                color='white', edgecolor='black', hatch='///', alpha=0.7)
        
        plt.xlabel('Value')
        plt.ylabel('Probability')
        
        title = exp_name.replace('_', ' ').title()
        title = title.replace('Rbt', 'RBT').replace('Stlc', 'STLC')
        plt.title(f'{title} ({target_type.capitalize()})')
        
        plt.legend()
        plt.grid(True, alpha=0.3)
        
        plt.savefig(output_path)
        plt.close()
    
    def run_single_experiment(self, experiment: Experiment) -> None:
        """Run a single experiment and generate its plots."""
        if self.verbose:
            print(f"\nRunning {experiment.name} experiment...")
        
        log_path = self.run_experiment(experiment.command)
        if self.verbose:
            print(f"Log file: {log_path}")
        
        initial_path, trained_path = self.parse_dist_paths(log_path)
        if self.verbose:
            print(f"Initial dist: {initial_path}")
            print(f"Trained dist: {trained_path}")
        
        initial_dist = self.read_distribution(initial_path)
        trained_dist = self.read_distribution(trained_path)
        
        if not initial_dist['val'].equals(trained_dist['val']):
            print("Error: Value columns do not match between initial and trained distributions")
            sys.exit(1)
        
        plot_path = os.path.join(self.output_dir, f"fig2_{experiment.name}.png")
        self.plot_distributions(initial_dist, trained_dist, plot_path, 
                              experiment.target_type, experiment.name)
        print(f"Plot saved to: {plot_path}")
    
    def copy_figure3_plots(self, log_dir: str) -> None:
        """Copy plots for figure 3 from the log directory."""
        feature_dist_pattern = os.path.join(log_dir, 'feature_dist_feature_spec_entropy_train_feature=true_freq=1-spb=5_prop=wellTyped_feature=typecheck_ft.png')
        unique_curves_pattern = os.path.join(log_dir, 'unique_curves_feature_spec_entropy_train_feature=true_freq=1-spb=5_prop=wellTyped_feature=typecheck_ft.svg')
        
        if self.verbose:
            print(f"Looking for plots in directory: {log_dir}")
            print(f"Searching for feature distribution plot: {feature_dist_pattern}")
        
        if not os.path.exists(feature_dist_pattern):
            print("Error: Could not find feature distribution plot")
            print("Contents of log directory:")
            for f in os.listdir(log_dir):
                print(f"  {f}")
            sys.exit(1)
        
        if self.verbose:
            print(f"Found feature distribution plot: {feature_dist_pattern}")
        output_path = os.path.join(self.output_dir, 'fig3a_stlc_unique_types_dist.png')
        shutil.copy2(feature_dist_pattern, output_path)
        print(f"Plot saved to: {output_path}")
        
        if self.verbose:
            print(f"Searching for unique curves plot: {unique_curves_pattern}")
        
        if not os.path.exists(unique_curves_pattern):
            print("Error: Could not find unique curves plot")
            print("Contents of log directory:")
            for f in os.listdir(log_dir):
                print(f"  {f}")
            sys.exit(1)
        
        if self.verbose:
            print(f"Found unique curves plot: {unique_curves_pattern}")
        output_path = os.path.join(self.output_dir, 'fig3b_stlc_cumulative_unique_types.svg')
        shutil.copy2(unique_curves_pattern, output_path)
        print(f"Plot saved to: {output_path}")

def run_experiments_parallel(experiments: List[Experiment], runner: ExperimentRunner) -> None:
    """Run experiments in parallel using multiprocessing."""
    num_workers = min(len(experiments), multiprocessing.cpu_count())
    pool = multiprocessing.Pool(processes=num_workers)
    pool.map(runner.run_single_experiment, experiments)
    pool.close()
    pool.join()

def create_figure2_experiments(args: argparse.Namespace) -> List[Experiment]:
    """Create the list of experiments for figure 2."""
    return [
        # RBT Type-Based Uniform
        Experiment(
            name='rbt_type_based_uniform',
            target_type='uniform',
            command=[
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangDerivedGenerator{RBT}(Main.ColorKVTree.t,Pair{Type,Integer}[Main.ColorKVTree.t=>4,Main.Color.t=>0],0,3,true)",
                f"Pair{{MLELossConfig{{RBT}},Float64}}[MLELossConfig{{RBT}}(depth,Uniform())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        ),
        # RBT Type-Based Linear
        Experiment(
            name='rbt_type_based_linear',
            target_type='linear',
            command=[
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangDerivedGenerator{RBT}(Main.ColorKVTree.t,Pair{Type,Integer}[Main.ColorKVTree.t=>4,Main.Color.t=>0],0,3,true)",
                f"Pair{{MLELossConfig{{RBT}},Float64}}[MLELossConfig{{RBT}}(depth,Linear())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        ),
        # STLC Type-Based Uniform
        Experiment(
            name='stlc_type_based_uniform',
            target_type='uniform',
            command=[
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangDerivedGenerator{STLC}(Main.Expr.t,Pair{Type,Integer}[Main.Expr.t=>5,Main.Typ.t=>2],0,3,true)",
                f"Pair{{MLELossConfig{{STLC}},Float64}}[MLELossConfig{{STLC}}(depth,Uniform())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        ),
        # STLC Type-Based Linear
        Experiment(
            name='stlc_type_based_linear',
            target_type='linear',
            command=[
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangDerivedGenerator{STLC}(Main.Expr.t,Pair{Type,Integer}[Main.Expr.t=>5,Main.Typ.t=>2],0,3,true)",
                f"Pair{{MLELossConfig{{STLC}},Float64}}[MLELossConfig{{STLC}}(depth,Linear())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        ),
        # STLC Bespoke Uniform
        Experiment(
            name='stlc_bespoke_uniform',
            target_type='uniform',
            command=[
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangBespokeSTLCGenerator(5,2)",
                f"Pair{{MLELossConfig{{STLC}},Float64}}[MLELossConfig{{STLC}}(depth,Uniform())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        ),
        # STLC Bespoke Linear
        Experiment(
            name='stlc_bespoke_linear',
            target_type='linear',
            command=[
                "julia", "--project", "pbt/experiments/tool.jl",
                "-f",
                "LangBespokeSTLCGenerator(5,2)",
                f"Pair{{MLELossConfig{{STLC}},Float64}}[MLELossConfig{{STLC}}(depth,Linear())=>{args.fig2_learning_rate}]",
                str(args.fig2_epochs),
                "0.0"
            ]
        )
    ]

def create_figure3_experiment(args: argparse.Namespace) -> Experiment:
    """Create the experiment for figure 3."""
    return Experiment(
        name='stlc_unique_types',
        command=[
            "julia", "--project", "pbt/experiments/tool.jl",
            "-f",
            "LangSiblingDerivedGenerator{STLC}(Main.Expr.t,Pair{Type,Integer}[Main.Expr.t=>5,Main.Typ.t=>2],2,3)",
            f"Pair{{FeatureSpecEntropy{{STLC}},Float64}}[FeatureSpecEntropy{{STLC}}(1,{args.fig3_epochs},wellTyped,typecheck_ft,true)=>{args.fig3_learning_rate}]",
            str(args.fig3_epochs),
            "0.0"
        ]
    )

def main():
    parser = argparse.ArgumentParser(description='Run experiments and generate distribution plots')
    parser.add_argument('--verbose', action='store_true', help='Print detailed file paths')
    parser.add_argument('--parallel', action='store_true', help='Run experiments in parallel')
    parser.add_argument('--all', action='store_true', help='Run all figures')
    parser.add_argument('--fig2', action='store_true', help='Run figure 2 experiments')
    parser.add_argument('--fig3', action='store_true', help='Run figure 3 experiment')
    parser.add_argument('--fast', action='store_true', help='Use faster training settings (fewer epochs, higher learning rates)')
    parser.add_argument('--fig2-learning-rate', type=float, help='Learning rate for figure 2 experiments')
    parser.add_argument('--fig2-epochs', type=int, help='Number of epochs for figure 2 experiments')
    parser.add_argument('--fig3-learning-rate', type=float, help='Learning rate for figure 3 experiment')
    parser.add_argument('--fig3-epochs', type=int, help='Number of epochs for figure 3 experiment')
    args, unknown = parser.parse_known_args()
    
    # Validate that at least one figure is selected
    if not (args.all or args.fig2 or args.fig3):
        print("Error: Must specify at least one figure to run. Use --all, --fig2, or --fig3.")
        sys.exit(1)
    
    # Check which figure-specific flags were explicitly specified
    fig2_flags_specified = any(arg.startswith('--fig2-') for arg in unknown)
    fig3_flags_specified = any(arg.startswith('--fig3-') for arg in unknown)
    
    # Validate that figure-specific parameters are only used when their figure is enabled
    if fig2_flags_specified and not (args.all or args.fig2):
        print("Error: Figure 2 parameters specified but figure 2 is not enabled. Use --fig2 or --all.")
        sys.exit(1)
    
    if fig3_flags_specified and not (args.all or args.fig3):
        print("Error: Figure 3 parameters specified but figure 3 is not enabled. Use --fig3 or --all.")
        sys.exit(1)
    
    # Set default parameters based on --fast flag
    if args.fast:
        # Fast defaults
        args.fig2_learning_rate = args.fig2_learning_rate if args.fig2_learning_rate is not None else 0.3
        args.fig2_epochs = args.fig2_epochs if args.fig2_epochs is not None else 100
        args.fig3_learning_rate = args.fig3_learning_rate if args.fig3_learning_rate is not None else 1.0
        args.fig3_epochs = args.fig3_epochs if args.fig3_epochs is not None else 200
    else:
        # Normal defaults
        args.fig2_learning_rate = args.fig2_learning_rate if args.fig2_learning_rate is not None else 0.1
        args.fig2_epochs = args.fig2_epochs if args.fig2_epochs is not None else 1000
        args.fig3_learning_rate = args.fig3_learning_rate if args.fig3_learning_rate is not None else 0.3
        args.fig3_epochs = args.fig3_epochs if args.fig3_epochs is not None else 2000
    
    # Create experiment runner
    runner = ExperimentRunner(verbose=args.verbose)
    
    # Create experiments
    figure2_experiments = create_figure2_experiments(args)
    figure3_experiment = create_figure3_experiment(args)
    
    # Run the requested figures
    if args.all:
        if args.parallel:
            # Run all experiments in parallel
            all_experiments = figure2_experiments + [figure3_experiment]
            run_experiments_parallel(all_experiments, runner)
            
            # After all experiments complete, copy the plots for figure 3
            log_path = runner.run_experiment(figure3_experiment.command)
            log_dir = os.path.dirname(log_path)
            runner.copy_figure3_plots(log_dir)
        else:
            # Run figures sequentially
            for exp in figure2_experiments:
                runner.run_single_experiment(exp)
            runner.run_single_experiment(figure3_experiment)
            log_path = runner.run_experiment(figure3_experiment.command)
            log_dir = os.path.dirname(log_path)
            runner.copy_figure3_plots(log_dir)
    else:
        if args.fig2:
            if args.parallel:
                run_experiments_parallel(figure2_experiments, runner)
            else:
                for exp in figure2_experiments:
                    runner.run_single_experiment(exp)
        if args.fig3:
            if args.parallel:
                run_experiments_parallel([figure3_experiment], runner)
                log_path = runner.run_experiment(figure3_experiment.command)
                log_dir = os.path.dirname(log_path)
                runner.copy_figure3_plots(log_dir)
            else:
                runner.run_single_experiment(figure3_experiment)
                log_path = runner.run_experiment(figure3_experiment.command)
                log_dir = os.path.dirname(log_path)
                runner.copy_figure3_plots(log_dir)

if __name__ == "__main__":
    main()

