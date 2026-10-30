"""2026-10-30: explicit case23 INITIAL47 completion; PREPARED, no auto-run.

Only --case23 runs prices.  Fixed U=sigma=7361/4000,L=173303/96000,
target27404839/66655000,V4,res2048, full sine and one fixed upper-moment G.
The existing evaluator is reused through a keyword context; no integrator
is copied here and no other rho cell, cutoff candidate, or mesh is searched.

Keep the certified [47,235/4],A4/5.  Fill [235/4,848/5] by FIVE precomputed
nodes b=min(5*a/4,848/5), each with the ONE free-cutoff rule
A=floor_.001(3*U/sqrt(a)), from the existing interval lower endpoint,
anchoring the physical first cutoff near 3 at the node's left endpoint.
Replace the failed right PARENT by [848/5,954/5] and [954/5,212],A2/5.
The parent remains failed in the read-only source history.  Its completed
endpoints are valid prices independently of that failed chord.

All FOUR matching completed source prices are reused literally, including
the two right endpoints.  Only ten middle prices and nu954/5,A2/5 are new:
at most ELEVEN cumulative new attempts.  The shared right midpoint is priced
once.  All E corrections, predecessor factors, roots and scores retain
Fraction nu and full I arithmetic in upper_moment_sine_nodes.py.

The EIGHT closed nodes must actually cover [47,212], with every joint strict,
before case23_arithmetic_connected becomes true.  The other three global
rho cells and entire INITIAL47 remain false.  Analytic actual-CF/CDF and
single-p3/2 endpoint bridges have passed the standard Lean build; external
interval-to-profile numerical certification remains separate.

Completed prices are atomically saved before node scoring.  First failure
stops the plan and preserves the complete remaining prepared domain, failed
parent and completed prices.  Resume requires a NEW output path.  There are
no per-cell snapshots or automatic retries/splits/refinements.  Old JSON,
sources and Lean are read-only.  Only elapsed metadata is floating point.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import time

import upper_moment_sine_nodes as engine


FORMAT = 'upper-moment-initial47-case23-completion-v1'
CONTEXT = engine.UpperMomentContext(U=F(7361, 4000), rhoLower=F(173303, 96000),
                                    target=F(27404839, 66655000))
MAX_NEW_PRICES = 11


def prepared_nodes() -> tuple[engine.SpectralNode, ...]:
    nodes, left, limit = [engine.PLANS[0]], F(235, 4), F(848, 5)
    for index in range(1, 6):
        assert left < limit
        right = min(F(5, 4)*left, limit)
        cutoff = 3*engine.rat(CONTEXT.U)/engine.rat(left).sqrt()
        A = F((1000*cutoff.lo)//engine.S, 1000)
        assert 0 < A < engine.V and A*A*left <= 9*CONTEXT.U**2
        nodes.append(engine.SpectralNode(f'case23-middle-{index:02d}', left, right, A))
        left = right
    assert left == limit
    nodes.extend((engine.SpectralNode('case23-right-848over5-to-954over5', F(848, 5), F(954, 5), F(2, 5)),
                  engine.SpectralNode('case23-right-954over5-to-212', F(954, 5), F(212), F(2, 5))))
    assert len(nodes) == 8 and nodes[0].left == 47 and nodes[-1].right == 212
    assert all(a.right == b.left for a, b in zip(nodes, nodes[1:]))
    return tuple(nodes)


def node_record(node: engine.SpectralNode) -> dict:
    record = node.record(context=CONTEXT)
    record['fixed_spectrum_parameters']['max_new_price_attempts'] = MAX_NEW_PRICES
    return record


def settings() -> dict:
    return {**engine.fixed_parameters(context=CONTEXT), 'max_new_price_attempts': MAX_NEW_PRICES,
            'case': '23', 'nu_domain': ['47', '212'], 'prepared_node_count': 8,
            'middle_A_rule': 'floor_.001(3*U/sqrt(a))', 'automatic_search_or_refinement': False}


class CompletionSession:
    def __init__(self, args):
        self.args, self.started = args, time.monotonic()
        self.plans = prepared_nodes()
        self.by_name = {node.name: node for node in self.plans}
        self.allowed = {engine.price_key(nu, node.A, context=CONTEXT): (node, nu)
                        for node in self.plans for nu in (node.left, node.right)}
        if args.output.exists():
            raise FileExistsError('Choose a NEW output path; existing results are read-only.')
        assert args.output.parent.exists() and args.seed_json.is_file()
        assert args.output.resolve() != args.seed_json.resolve()
        if args.resume_from:
            assert args.output.resolve() != args.resume_from.resolve()
            self.record = json.loads(args.resume_from.read_text(encoding='utf-8'))
            assert self.record['format'] == FORMAT and self.record['model'] == engine.MODEL
            assert self.record['settings'] == settings()
            assert self.record['plans'] == [node_record(node) for node in self.plans]
        else:
            self.record = {'format': FORMAT, 'date': '2026-10-30', 'model': engine.MODEL,
                           'settings': settings(), 'plans': [node_record(node) for node in self.plans],
                           'completed_prices': {}, 'price_attempts': [], 'node_attempts': [], 'proved_nodes': [],
                           'new_price_attempts': 0, 'active_price_key': None, 'active_price_attempt_index': None,
                           'active_node_index': None, 'terminal_failure': False, 'stop_reason': None,
                           'actual_CF_CDF_single_three_halves_endpoint_bridge_Lean_proved': True,
                           'analytic_Lean_source': 'BerryEsseen.UpperMomentSpectrumPrice',
                           'numerical_interval_to_profile_Lean_proved': False,
                           'formal_lean_numerical_theorem': False,
                           'other_three_global_rho_cells_certified': False, 'entire_INITIAL47_certified': False,
                           'complete_classical_formula_claimed': False, 'noninteger_iid_sum_claimed': False}
        self.engines = {node.A: engine.UpperMomentSineEvaluator(
            node.A, self.record['completed_prices'], context=CONTEXT) for node in self.plans}
        self.load_seed()
        self.validate_state()
        for pointer, collection in (('active_price_attempt_index', 'price_attempts'),
                                    ('active_node_index', 'node_attempts')):
            index = self.record[pointer]
            if index is not None:
                if self.record[collection][index]['status'] == 'in-progress':
                    self.record[collection][index]['status'] = 'interrupted'
                self.record[pointer] = None
        self.record['active_price_key'] = None
        for evaluator in self.engines.values():
            evaluator.on_change, evaluator.on_part = self.atomic_save, self.save_part
        self.atomic_save()

    def load_seed(self):
        old = json.loads(self.args.seed_json.read_text(encoding='utf-8'))
        assert old['format'] == engine.FORMAT and old['model'] == engine.MODEL
        assert old['fixed_parameters'] == engine.fixed_parameters(context=CONTEXT)
        assert old['plans'] == [node.record() for node in engine.PLANS]
        assert old['terminal_failure'] is True
        assert len(old['completed_prices']) == 4
        for key, value in old['completed_prices'].items():
            node, nu = self.allowed[key]
            self.engines[node.A].validate(value)
            assert value['parameters'] == engine.physical_parameters(nu, node.A, context=CONTEXT)
            if key in self.record['completed_prices']:
                assert self.record['completed_prices'][key] == value
            else:
                self.record['completed_prices'][key] = deepcopy(value)
        # A failed chord does not invalidate either of its complete endpoint prices.
        self.record['read_only_source'] = self.args.seed_json.name
        self.record['source_node_attempts_preserved'] = deepcopy(old['node_attempts'])
        self.record['source_failed_parent_preserved'] = [deepcopy(a) for a in old['node_attempts'] if a['status'] == 'failed']
        assert len(self.record['source_failed_parent_preserved']) == 1
        parent = self.record['source_failed_parent_preserved'][0]
        assert parent['strict_joint'] is False and parent['name'] == engine.PLANS[1].name
        self.record['literal_reused_source_price_keys'] = list(old['completed_prices'])
        first = self.plans[0]
        source = next(a for a in old['proved_nodes'] if a['name'] == first.name)
        self.validate_joint(source, first, source_node_record=first.record())
        if not any(a['name'] == first.name for a in self.record['proved_nodes']):
            reused = deepcopy(source)
            reused.update({'node': node_record(first), 'origin': self.args.seed_json.name, 'whole_node_reused': True})
            self.record['node_attempts'].append(reused)
            self.record['proved_nodes'].append(reused)

    def validate_joint(self, attempt: dict, node: engine.SpectralNode, *, source_node_record=None):
        assert attempt['node'] == (node_record(node) if source_node_record is None else source_node_record)
        keys = [engine.price_key(nu, node.A, context=CONTEXT) for nu in (node.left, node.right)]
        assert attempt['endpoint_keys'] == keys and attempt['status'] == 'passed' and attempt['strict_joint'] is True
        theta = engine.RMAX*(node.right-node.left)**2/(8*node.left**2)
        assert 0 <= theta < 1 and F(attempt['theta']) == theta and F(attempt['factor']) == 1/(1-theta)
        joint = max(engine.score(self.record['completed_prices'][key]) for key in keys)/(1-theta)
        p = attempt['joint_upper']
        assert F(int(p['upper_numerator']), int(p['denominator'])) == joint < CONTEXT.target

    def validate_state(self):
        for key, value in self.record['completed_prices'].items():
            node, nu = self.allowed[key]
            self.engines[node.A].validate(value)
            assert value['parameters'] == engine.physical_parameters(nu, node.A, context=CONTEXT)
        assert len(self.record['price_attempts']) == self.record['new_price_attempts'] <= MAX_NEW_PRICES
        for attempt in self.record['price_attempts']:
            node, nu = self.allowed[attempt['key']]
            assert attempt['parameters'] == engine.physical_parameters(nu, node.A, context=CONTEXT)
        seen = set()
        for attempt in self.record['proved_nodes']:
            node = self.by_name[attempt['name']]
            assert node.name not in seen
            seen.add(node.name)
            self.validate_joint(attempt, node)

    def atomic_save(self):
        passed = {a['name'] for a in self.record['proved_nodes']}
        remaining = [node for node in self.plans if node.name not in passed]
        self.record['remaining_prepared_nodes'] = [node_record(node) for node in remaining]
        self.record['unresolved_case23_nu_domain'] = [[str(node.left), str(node.right)] for node in remaining]
        closed = sorted((node.left, node.right) for node in self.plans if node.name in passed)
        cursor = F(47)
        for left, right in closed:
            if left > cursor:
                break
            cursor = max(cursor, right)
        all_strict = all(F(int(a['joint_upper']['upper_numerator']), int(a['joint_upper']['denominator'])) < CONTEXT.target
                         for a in self.record['proved_nodes'])
        self.record['case23_arithmetic_connected'] = not remaining and len(passed) == 8 and cursor == 212 and all_strict
        self.record['current_invocation_elapsed_seconds_metadata'] = time.monotonic()-self.started
        engine_node_atomic_save(self.args.output, self.record)

    def save_part(self, key: str, name: str, part: dict, next_stage: str):
        index = self.record['active_price_attempt_index']
        assert index is not None and self.record['price_attempts'][index]['key'] == key
        attempt = self.record['price_attempts'][index]
        attempt['completed_absolute_terms'][name] = part
        attempt['active_stage'] = next_stage
        self.atomic_save()

    def evaluate(self, node: engine.SpectralNode, nu: F):
        evaluator, key = self.engines[node.A], engine.price_key(nu, node.A, context=CONTEXT)
        if key in self.record['completed_prices']:
            return evaluator.evaluate(nu)
        if self.record['new_price_attempts'] >= MAX_NEW_PRICES:
            raise RuntimeError('Cumulative ELEVEN new-price attempt limit reached.')
        attempt = {'key': key, 'parameters': engine.physical_parameters(nu, node.A, context=CONTEXT),
                   'status': 'in-progress', 'active_stage': 'first-ODE', 'completed_absolute_terms': {}}
        self.record['price_attempts'].append(attempt)
        self.record['new_price_attempts'] += 1
        self.record['active_price_key'] = key
        self.record['active_price_attempt_index'] = len(self.record['price_attempts'])-1
        self.atomic_save()
        try:
            value = evaluator.evaluate(nu)
        except BaseException as error:
            attempt.update({'status': 'interrupted' if isinstance(error, KeyboardInterrupt) else 'failed',
                            'error_kind': type(error).__name__, 'error_message': str(error)})
            self.record['active_price_key'] = self.record['active_price_attempt_index'] = None
            self.atomic_save()
            raise
        attempt.update({'status': 'completed', 'active_stage': None})
        self.record['active_price_key'] = self.record['active_price_attempt_index'] = None
        self.atomic_save()
        return value

    def stop(self, attempt: dict, reason: str, **details):
        attempt.update({'status': 'failed', 'failure': reason, **details})
        self.record.update({'terminal_failure': True, 'stop_reason': reason, 'active_node_index': None})
        self.atomic_save()

    def run(self):
        if self.record['terminal_failure']:
            return
        for node in self.plans:
            if any(a['name'] == node.name for a in self.record['proved_nodes']):
                continue
            keys = [engine.price_key(nu, node.A, context=CONTEXT) for nu in (node.left, node.right)]
            attempt = {'name': node.name, 'node': node_record(node), 'status': 'in-progress',
                       'endpoint_keys': keys, 'obtained_endpoint_keys': []}
            self.record['node_attempts'].append(attempt)
            self.record['active_node_index'] = len(self.record['node_attempts'])-1
            self.atomic_save()
            values = []
            for nu, key in zip((node.left, node.right), keys):
                try:
                    value = self.evaluate(node, nu)
                except Exception as error:
                    self.stop(attempt, 'endpoint arithmetic or cumulative budget failed; no automatic retry',
                              failed_price_key=key, error_kind=type(error).__name__, error_message=str(error))
                    return
                attempt['obtained_endpoint_keys'].append(key)
                values.append(value)
                if engine.score(value) >= CONTEXT.target:
                    self.stop(attempt, 'endpoint not strict; no automatic refinement', failed_price_key=key)
                    return
                self.atomic_save()
            theta = engine.RMAX*(node.right-node.left)**2/(8*node.left**2)
            assert 0 <= theta < 1
            factor = 1/(1-theta)
            joint = max(engine.score(value) for value in values)*factor
            attempt.update({'rmax': str(engine.RMAX), 'theta': str(theta), 'factor': str(factor),
                            'joint_upper': engine.record_fraction(joint), 'strict_joint': joint < CONTEXT.target})
            if joint >= CONTEXT.target:
                self.stop(attempt, 'Fraction chord joint not strict; no automatic refinement')
                return
            attempt['status'] = 'passed'
            self.record['active_node_index'] = None
            self.record['proved_nodes'].append(attempt)
            self.atomic_save()
            print(json.dumps({'node': node.name, 'nu': [str(node.left), str(node.right)], 'A': str(node.A),
                              'joint_upper': attempt['joint_upper']['decimal_upper'], 'strict_joint': True}), flush=True)


def engine_node_atomic_save(path: Path, record: dict):
    # 2026-10-30: same sibling-temp/fsync/replace checkpoint used by the engine.
    import os
    temp = path.with_name(path.name+'.tmp')
    with temp.open('w', encoding='utf-8', newline='\n') as handle:
        json.dump(record, handle, indent=2)
        handle.write('\n')
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temp, path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case23', action='store_true', help='Explicitly run only the fixed case23 completion.')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--resume-from', type=Path, help='Matching completion checkpoint; output must be new.')
    parser.add_argument('--seed-json', type=Path, default=Path(__file__).with_name('upper_moment_sine_nodes.json'))
    args = parser.parse_args()
    if not args.case23:
        parser.error('Use --case23 explicitly after source review; no prices by default.')
    engine.scalar.base.pin_two_cpus()
    session = CompletionSession(args)
    session.run()
    print(json.dumps({'case23_arithmetic_connected': session.record['case23_arithmetic_connected'],
                      'new_price_attempts': session.record['new_price_attempts'], 'stop_reason': session.record['stop_reason'],
                      'unresolved_case23_nu_domain': session.record['unresolved_case23_nu_domain'],
                      'other_three_global_rho_cells_certified': False, 'entire_INITIAL47_certified': False}), flush=True)


if __name__ == '__main__':
    main()
