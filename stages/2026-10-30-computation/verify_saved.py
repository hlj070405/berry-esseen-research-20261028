#!/usr/bin/env python3
"""2026-10-30: verify saved INITIAL47 arithmetic, without rerunning integrals.

Checks exact parameters, four-term sums, outward normalization, reuse history,
failed-parent arithmetic, endpoint chords, Gaussian gates, and the final cover.
This is an external Python check, not Lean numerical certification.
"""
from __future__ import annotations

from copy import deepcopy
from fractions import Fraction as F
import argparse
import json
from pathlib import Path
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'src'
SAVED = ROOT / 'saved'
sys.dont_write_bytecode = True
sys.path.insert(0, str(SOURCE))

import n47_upper_moment_global_sine_pilot as pilot
import upper_moment_sine_nodes as engine
import upper_moment_initial47_completion as completion
import upper_moment_initial47_remaining as remaining
import join_initial47_own_score as join
import upper_moment_finite_affine_cover as affine
import continue_upper_moment_finite_affine as fine

LOCAL_MODULES = (
    'n4_band_interval_certificate', 'finite_n_closed_rho_box_pilots',
    'rational_kernel_endpoint_probe', 'order8_rational_ray_endpoint_probe',
    'n15_reference_circle_boundary_probe', 'n47_upper_moment_global_sine_pilot',
    'upper_moment_sine_nodes', 'upper_moment_initial47_completion',
    'upper_moment_initial47_remaining', 'join_initial47_own_score',
    'upper_moment_finite_affine_cover', 'continue_upper_moment_finite_affine',
)
FILES = (
    'n47_upper_moment_global_sine_pilot.json', 'upper_moment_sine_nodes.json',
    'upper_moment_initial47_completion.json', 'upper_moment_initial47_remaining.json',
    'join_initial47_own_score.json',
    'upper_moment_finite_affine_cover.json', 'continue_upper_moment_finite_affine.json',
)


def exact(piece):
    return F(int(piece['upper_numerator']), int(piece['denominator']))


def check_rendered_fractions(value):
    if isinstance(value, dict):
        if {'upper_numerator', 'denominator', 'decimal_upper'} <= value.keys():
            assert value['decimal_upper'] == engine.rat(exact(value)).decimal_upper()
        for child in value.values():
            check_rendered_fractions(child)
    elif isinstance(value, list):
        for child in value:
            check_rendered_fractions(child)


def check_attempts(record, expected_count):
    assert record['new_price_attempts'] == len(record['price_attempts']) == expected_count
    seen = set()
    for attempt in record['price_attempts']:
        key = attempt['key']
        assert key not in seen
        seen.add(key)
        result = record['completed_prices'][key]
        assert attempt['status'] == 'completed' and attempt['active_stage'] is None
        assert attempt['parameters'] == result['parameters']
        assert attempt['completed_absolute_terms'] == dict(zip(
            ('T1', 'T2', 'T3', 'T4'), result['parts_delta_upper']))
    assert record['active_price_key'] is record['active_price_attempt_index'] is None


def verify_affine(results_dir, coarse, continuation):
    assert coarse['format'] == affine.FORMAT and coarse['model'] == engine.MODEL
    assert coarse['settings'] == affine.AffineSession.settings()
    assert len(coarse['rounds']) == 8 and len(coarse['completed_prices']) == 24
    assert coarse['terminal_failure'] is True
    assert coarse['stop_reason'] == 'Fixed eight-round limit reached; unresolved domain preserved.'
    assert coarse['finite31_through46_affine_T_envelope_arithmetic_certified'] is False
    old_session = affine.AffineSession.__new__(affine.AffineSession)
    old_session.record, old_session.engines, old_session.allowed = coarse, {}, {}
    old_session.validate_state()
    check_attempts(coarse, 24)
    expected_segments = []
    cursor = affine.RHO_TOP
    for row in coarse['rounds']:
        assert row['status'] == 'completed' and F(row['U']) == cursor
        context, _, nodes = affine.round_parameters(cursor)
        assert {a['name'] for a in row['proved_nodes']} == {node.name for node in nodes}
        B = max(exact(a['joint_upper']) for a in row['proved_nodes'])
        lower, threshold = affine.lower_from_B(B)
        assert row['B_upper'] == engine.record_fraction(B)
        assert F(row['unrounded_lower_threshold']) == threshold and F(row['L']) == lower < cursor
        assert row['all_three_affine_budgets_paid'] is True
        assert all(B <= a*lower+b for a, b in affine.BUDGETS)
        expected_segments.append({'rho_lower': str(lower), 'rho_upper': str(cursor),
                                  'B_upper': row['B_upper']})
        cursor = lower
    assert expected_segments == coarse['covered_closed_rho_segments']
    assert cursor == fine.OLD_FRONTIER
    assert coarse['unresolved_rho_domain'] == [[str(affine.RHO_BOTTOM), str(cursor)]]

    assert continuation['format'] == fine.FORMAT and continuation['model'] == engine.MODEL
    assert continuation['settings'] == fine.ContinuationSession.settings()
    assert len(continuation['rounds']) == 4 and len(continuation['completed_prices']) == 41
    assert continuation['terminal_failure'] is False
    assert continuation['finite31_through46_affine_T_envelope_arithmetic_certified'] is True
    assert continuation['seed_rounds'] == coarse['rounds']
    assert continuation['seed_closed_segments'] == expected_segments
    assert continuation['seed_price_keys'] == list(coarse['completed_prices'])
    assert continuation['source_stop_reason_preserved'] == coarse['stop_reason']
    for key, value in coarse['completed_prices'].items():
        assert continuation['completed_prices'][key] == value
    fs = fine.ContinuationSession.__new__(fine.ContinuationSession)
    fs.record, fs.engines, fs.allowed = deepcopy(continuation), {}, {}
    fs.args = SimpleNamespace(seed_json=results_dir / 'upper_moment_finite_affine_cover.json')
    fs.load_seed()
    fs.validate_state()
    check_attempts(continuation, 17)
    assert len(continuation['anchor_three_literal_price_keys']) == 3
    assert all(key in coarse['completed_prices'] for key in continuation['anchor_three_literal_price_keys'])
    assert continuation['unresolved_rho_domain'] == []
    assert continuation['closed_union_rho_segments'] == [[str(affine.RHO_BOTTOM), str(affine.RHO_TOP)]]
    assert F(continuation['frontier_connected_to_rho0']) == affine.RHO_BOTTOM
    segments = [(F(s['rho_lower']), F(s['rho_upper'])) for s in expected_segments]
    for row in continuation['rounds']:
        U = F(row['U'])
        context, _, nodes = fine.fine_parameters(U)
        assert row['status'] == 'completed' and row['affine_segment_certified'] is True
        assert {a['name'] for a in row['proved_nodes']} == {node.name for node in nodes}
        B = max(exact(a['joint_upper']) for a in row['proved_nodes'])
        lower, threshold = affine.lower_from_B(B)
        assert row['B_upper'] == engine.record_fraction(B)
        assert F(row['unrounded_lower_threshold']) == threshold and F(row['L']) == lower <= U
        assert row['all_three_affine_budgets_paid'] is True
        assert all(B <= a*lower+b for a, b in affine.BUDGETS)
        before = fine.frontier(segments)
        segments.append((lower, U))
        assert F(row['frontier_before']) == before
        assert F(row['frontier_after_candidate']) == fine.frontier(segments) < before
    assert fine.closed_union(segments) == [(affine.RHO_BOTTOM, affine.RHO_TOP)]
    for record in (coarse, continuation):
        for value in record['completed_prices'].values():
            assert value['parameters']['rhoLower'] == '1'
            assert affine.absolute_B(value) == engine.score(value)
        assert record['actual_rho_equals_one_assumed'] is False
        assert record['formal_lean_numerical_theorem'] is False
        assert record['all_n_classical_formula_claimed'] is False
        assert record['original_guess_certified'] is False
    assert continuation['CF_prices_assume_hprev'] is False
    return continuation['completed_prices']


def verify(results_dir: Path) -> dict:
    assert not sys.flags.optimize, 'Run without -O: assertions are part of this verifier.'
    for name in LOCAL_MODULES:
        assert Path(sys.modules[name].__file__).resolve().parent == SOURCE
    results_dir = results_dir.resolve()
    records = [json.loads((results_dir / name).read_text(encoding='utf-8')) for name in FILES]
    old, two, last, rest, saved_join, coarse, continuation = records
    for record in records:
        check_rendered_fractions(record)

    # This rebuilds parameter enclosures only, never the 2048-cell integrations.
    assert old['format'] == pilot.FORMAT and old['model'] == pilot.MODEL
    assert old['status'] == 'completed' and old['active_stage'] is None
    assert old['parameters'] == pilot.UpperMomentN47Pilot().parameters()
    evaluation = old['evaluation']
    parts = evaluation['parts_delta_upper']
    assert len(parts) == 4
    assert old['completed_absolute_terms'] == dict(zip(('T1', 'T2', 'T3', 'T4'), parts))
    assert all(p['denominator'] == str(engine.S) and int(p['upper_numerator']) >= 0 for p in parts)
    total = sum(int(p['upper_numerator']) for p in parts)
    assert evaluation['delta_upper'] == engine.scalar.base.rational_text(engine.I(total, total))
    ratio = (engine.rat(F(47)).sqrt()*engine.I(total, total)/engine.rat(engine.RHO_LOWER)).upper()
    assert evaluation['sqrt_n_delta_over_rho_lower_upper'] == engine.scalar.base.rational_text(ratio)
    assert F(ratio.hi, engine.S) < engine.TARGET
    assert evaluation['arithmetic_strict_success_given_pending_bridges'] is True
    assert evaluation['strict_margin_lower_numerator'] == str((engine.rat(engine.TARGET)-ratio).lo)
    assert old['formal_lean_numerical_theorem'] is False

    assert two['format'] == engine.FORMAT and two['model'] == engine.MODEL
    assert two['fixed_parameters'] == engine.fixed_parameters()
    assert two['plans'] == [node.record() for node in engine.PLANS]
    assert len(two['completed_prices']) == 4 and two['terminal_failure'] is True
    assert two['formal_lean_numerical_theorem'] is False
    node_session = engine.NodeSession.__new__(engine.NodeSession)
    node_session.args = SimpleNamespace(seed_json=results_dir / FILES[0])
    node_session.record = deepcopy(two)
    node_session.allowed = {engine.price_key(nu, node.A): (node, nu)
                            for node in engine.PLANS for nu in (node.left, node.right)}
    node_session.engines = {node.A: engine.UpperMomentSineEvaluator(
        node.A, node_session.record['completed_prices']) for node in engine.PLANS}
    node_session.load_pilot_seed()
    node_session.validate_history()
    check_attempts(two, 3)
    assert len(two['proved_nodes']) == 1 and len(two['node_attempts']) == 2
    assert two['node_attempts'][0] == two['proved_nodes'][0]
    failed = two['node_attempts'][1]
    parent = engine.PLANS[1]
    assert failed['name'] == parent.name and failed['node'] == parent.record()
    assert failed['status'] == 'failed' and failed['strict_joint'] is False
    keys = [engine.price_key(nu, parent.A) for nu in (parent.left, parent.right)]
    assert failed['endpoint_keys'] == failed['obtained_endpoint_keys'] == keys
    theta = engine.RMAX*(parent.right-parent.left)**2/(8*parent.left**2)
    joint = max(engine.score(two['completed_prices'][key]) for key in keys)/(1-theta)
    assert F(failed['theta']) == theta and F(failed['factor']) == 1/(1-theta)
    assert exact(failed['joint_upper']) == joint >= engine.TARGET
    assert all(engine.score(two['completed_prices'][key]) < engine.TARGET for key in keys)
    assert two['two_prepared_nodes_arithmetic_certified_given_pending_bridges'] is False

    assert last['format'] == completion.FORMAT and last['model'] == engine.MODEL
    assert last['settings'] == completion.settings()
    plans = completion.prepared_nodes()
    assert last['plans'] == [completion.node_record(node) for node in plans]
    assert len(last['completed_prices']) == 15 and last['terminal_failure'] is False
    assert last['case23_arithmetic_connected'] is True and len(last['proved_nodes']) == 8
    assert last['source_node_attempts_preserved'] == two['node_attempts']
    assert last['source_failed_parent_preserved'] == [failed]
    assert last['literal_reused_source_price_keys'] == list(two['completed_prices'])
    for key, value in two['completed_prices'].items():
        assert last['completed_prices'][key] == value  # Literal reuse, failed parent unchanged.
    cs = completion.CompletionSession.__new__(completion.CompletionSession)
    cs.record, cs.plans = last, plans
    cs.by_name = {node.name: node for node in plans}
    cs.allowed = {engine.price_key(nu, node.A, context=completion.CONTEXT): (node, nu)
                  for node in plans for nu in (node.left, node.right)}
    cs.engines = {node.A: engine.UpperMomentSineEvaluator(
        node.A, last['completed_prices'], context=completion.CONTEXT) for node in plans}
    cs.validate_state()
    check_attempts(last, 11)
    assert last['unresolved_case23_nu_domain'] == last['remaining_prepared_nodes'] == []
    assert last['formal_lean_numerical_theorem'] is False and last['entire_INITIAL47_certified'] is False

    cases = remaining.cases()
    entries = remaining.prepared_entries(cases)
    assert rest['format'] == remaining.FORMAT and rest['model'] == engine.MODEL
    assert rest['cases'] == [case.record() for case in cases]
    assert rest['plans'] == [entry.record() for entry in entries]
    assert len(rest['completed_prices']) == 13 and len(rest['proved_entries']) == 7
    assert rest['terminal_failure'] is False and rest['three_remaining_cells_arithmetic_certified'] is True
    assert rest['case_arithmetic_certified'] == {'20': True, '21': True, '22': True}
    assert rest['remaining_by_case'] == {'20': [], '21': [], '22': []}
    rs = remaining.RemainingSession.__new__(remaining.RemainingSession)
    rs.record, rs.entries, rs.cases = rest, entries, cases
    rs.by_name = {entry.name: entry for entry in entries}
    rs.allowed = {engine.price_key(nu, entry.A, context=entry.case.context): (entry, nu)
                  for entry in entries for nu in entry.endpoints()}
    rs.engines = {(entry.case.context, entry.A): engine.UpperMomentSineEvaluator(
        entry.A, rest['completed_prices'], context=entry.case.context) for entry in entries}
    rs.validate_state()
    check_attempts(rest, 13)
    assert rest['formal_lean_numerical_theorem'] is False and rest['entire_INITIAL47_certified'] is False

    distinct = {**last['completed_prices'], **rest['completed_prices']}
    assert len(distinct) == 28
    assert set(last['completed_prices']).isdisjoint(rest['completed_prices'])
    # The original collector rechecks every endpoint, chord, Gaussian cutoff,
    # and closed-domain join using THIS results directory exclusively.
    assembled = join.collect(results_dir)
    assert assembled == saved_join
    assert assembled['requires_sharp_all_law_predecessor'] is True
    assert assembled['all_classical_INITIAL47_own_score_inputs_replaced_in_real_arithmetic'] is True
    assert assembled['finite_CF_index_cell_pairs'] == 240
    assert assembled['nondegenerate_CF_nodes'] == 14 and assembled['single_integer_points'] == 1
    assert assembled['source_failed_chord_retained'] == [failed]
    for field in ('original_support_or_charged_premises_eliminated',
                  'entire_INITIAL47_certificate_newly_proved', 'formal_lean_numerical_prices',
                  'full_conjecture_Lean_proved'):
        assert assembled[field] is False
    finite_prices = verify_affine(results_dir, coarse, continuation)
    assert set(distinct).isdisjoint(finite_prices) and len({**distinct, **finite_prices}) == 69
    return {'saved_arithmetic_verified': True, 'distinct_endpoint_prices': 69,
            'INITIAL47_endpoint_prices': len(distinct), 'finite31_46_endpoint_prices': len(finite_prices),
            'closed_nodes': 14, 'single_integer_points': 1, 'finite_index_cell_pairs': 240,
            'INITIAL47_requires_original_sharp_predecessor': True,
            'finite31_46_closed_rho_union': ['8/5', '7361/4000'],
            'finite31_46_CF_requires_sharp_predecessor': False, 'Lean_numerical_certification': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results-dir', type=Path, default=SAVED)
    args = parser.parse_args()
    print(json.dumps(verify(args.results_dir), indent=2))


if __name__ == '__main__':
    main()
