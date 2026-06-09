#!/bin/bash
#SBATCH --job-name=trace_mathlib
#SBATCH --output=logs/trace_mathlib.out
#SBATCH --error=logs/trace_mathlib.err
#SBATCH --cpus-per-task=64
#SBATCH --time=2-00:00:00
#SBATCH --mem=100G
#SBATCH --gres=gpu:1
#SBATCH --partition=general


set -e  # Exit on error

# ============ Environment Setup ============
cd ~/lean-training-data
source .venv/bin/activate


# ============ Run the Script ============

python scripts/step_tactics_dataframe.py
