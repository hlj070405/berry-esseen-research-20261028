#!/usr/bin/env python3
"""2026-10-30: recompute the fixed INITIAL47 sequence into a new result directory.

Runs INITIAL47 and then the finite31..46 coarse/fine affine cover, preserving
the expected failed chord and coarse budget stop. All seeds and the collector
point to this invocation's new results. No saved price is imported.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'src'
BOOTSTRAP = (
    "import runpy,sys; sys.path.insert(0,sys.argv.pop(1)); "
    "sys.argv.pop(0); runpy.run_path(sys.argv[0],run_name='__main__')"
)


def run(script, *arguments):
    subprocess.run([sys.executable, '-I', '-B', '-c', BOOTSTRAP, str(SOURCE),
                    str(SOURCE / script), *map(str, arguments)], check=True, cwd=ROOT)


def load(results, name):
    return json.loads((results / name).read_text(encoding='utf-8'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results-dir', type=Path, required=True, help='New or empty output directory.')
    parser.add_argument('--stop-after', choices=('pilot', 'two-node', 'case23', 'remaining',
                                                'initial47', 'affine-coarse', 'all'),
                        default='all', help='Optional bounded rerun; default runs all 69 endpoint prices.')
    args = parser.parse_args()
    if sys.flags.optimize:
        parser.error('Run without -O: assertions are required.')
    results = args.results_dir.resolve()
    saved = (ROOT / 'saved').resolve()
    if results == ROOT or results == SOURCE or results == saved or results.is_relative_to(saved):
        parser.error('Choose a new result directory outside the saved data and source.')
    if results.exists() and (not results.is_dir() or any(results.iterdir())):
        parser.error('Output directory must be new or empty; existing results will not be overwritten.')
    results.mkdir(parents=True, exist_ok=True)
    pilot = results / 'n47_upper_moment_global_sine_pilot.json'
    nodes = results / 'upper_moment_sine_nodes.json'
    case23 = results / 'upper_moment_initial47_completion.json'
    rest = results / 'upper_moment_initial47_remaining.json'
    run('n47_upper_moment_global_sine_pilot.py', '--pilot', '--output', pilot)
    assert load(results, pilot.name)['status'] == 'completed'
    if args.stop_after == 'pilot':
        return
    run('upper_moment_sine_nodes.py', '--nodes', '--output', nodes, '--seed-json', pilot)
    two = load(results, nodes.name)
    assert two['terminal_failure'] is True and two['new_price_attempts'] == 3
    assert len(two['completed_prices']) == 4
    assert len(two['proved_nodes']) == 1
    assert two['node_attempts'][-1]['status'] == 'failed'
    assert two['node_attempts'][-1]['strict_joint'] is False
    if args.stop_after == 'two-node':
        return
    run('upper_moment_initial47_completion.py', '--case23', '--output', case23, '--seed-json', nodes)
    assert load(results, case23.name)['case23_arithmetic_connected'] is True
    if args.stop_after == 'case23':
        return
    run('upper_moment_initial47_remaining.py', '--remaining', '--output', rest)
    assert load(results, rest.name)['three_remaining_cells_arithmetic_certified'] is True
    if args.stop_after == 'remaining':
        return
    run('join_initial47_own_score.py', '--results-dir', results)
    if args.stop_after == 'initial47':
        return
    coarse = results / 'upper_moment_finite_affine_cover.json'
    run('upper_moment_finite_affine_cover.py', '--cover', '--output', coarse)
    coarse_data = load(results, coarse.name)
    assert coarse_data['new_price_attempts'] == len(coarse_data['completed_prices']) == 24
    assert coarse_data['terminal_failure'] is True
    assert coarse_data['finite31_through46_affine_T_envelope_arithmetic_certified'] is False
    assert coarse_data['stop_reason'] == 'Fixed eight-round limit reached; unresolved domain preserved.'
    if args.stop_after == 'affine-coarse':
        return
    continued = results / 'continue_upper_moment_finite_affine.json'
    run('continue_upper_moment_finite_affine.py', '--continue-cover', '--output', continued, '--seed-json', coarse)
    assert load(results, continued.name)['finite31_through46_affine_T_envelope_arithmetic_certified'] is True
    subprocess.run([sys.executable, '-I', '-B', str(ROOT / 'verify_saved.py'),
                    '--results-dir', str(results)], check=True, cwd=ROOT)


if __name__ == '__main__':
    main()
