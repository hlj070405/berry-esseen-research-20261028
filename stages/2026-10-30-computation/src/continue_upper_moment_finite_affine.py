"""2026-10-30: minimal fine-nu continuation of the finite n31..46 T cover.

Prepared only: --continue-cover explicitly runs new prices.  Old source and
JSON remain read-only; the unchanged evaluator and original BUDGETS,
absolute_B and lower_from_B are reused, with no integrator copied here.

Preserve all eight coarse closed moment segments and all 24 completed prices.
First NEW round anchors at the OLD last-round U=832603/500000, rather than
its frontier 331271/200000, to reuse its three endpoint prices literally.
At fixed A=3U/5,context sigma=U,rhoLower=1 and the same Gamma/G/W, use four
nu nodes with endpoints 31,279/8,155/4,339/8,46.  Nonintegers are spectral
endpoints only.  The first fine round needs only the two new midpoints.

B=max(four genuine-CDF/profile chord bounds), with the original p3/2 factor
and the original three affine budgets/ceil_1e-6 rule for L.  The certified
closed [L,U] may overlap old segments.  A completed new round must lower the
ACTUAL union frontier connected to rho0; merely L<Uanchor is insufficient.
Subsequent U=L, with the same four nu nodes and five prices per round.
At most FOUR new rounds and SEVENTEEN new attempts (2+3*5), cumulatively.
Stop on the first point/joint/arithmetic failure or absent frontier progress.

Completed prices are durable before scoring.  All old and new proved closed
segments remain available, including a valid overlapping segment that does
not advance the frontier.  Exact closed-interval union decides completion
of [8/5,rho0] for all actual n31..46.  No changed target, new Gaussian mask,
hprev assumption, all-n formula or original-conjecture claim is introduced.
Numerical bounds remain external arithmetic, not Lean numerical theorems.
Resume requires a NEW output path; only matching complete prices are reused.
No per-cell logs, parameter candidates, reports or helper files.  Elapsed
metadata alone is floating point.  The old budget stop is not a math failure.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import time

import upper_moment_finite_affine_cover as original


engine = original.engine
FORMAT = 'continue-upper-moment-finite31-46-fine-nu-v1'
ANCHOR, OLD_FRONTIER = F(832603, 500000), F(331271, 200000)
MAX_NEW_ROUNDS, MAX_NEW_PRICES = 4, 17
NU_ENDPOINTS = (F(31), F(279, 8), F(155, 4), F(339, 8), F(46))


def fine_parameters(U: F):
    context, A, _ = original.round_parameters(U)
    nodes = tuple(engine.SpectralNode(f'fine-nu-{a}-to-{b}', a, b, A)
                  for a, b in zip(NU_ENDPOINTS, NU_ENDPOINTS[1:]))
    return context, A, nodes


def closed_union(segments: list[tuple[F, F]]) -> list[tuple[F, F]]:
    merged = []
    for left, right in sorted(segments):
        assert original.RHO_BOTTOM <= left <= right <= original.RHO_TOP
        if merged and left <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], right))
        else:
            merged.append((left, right))
    return merged


def frontier(segments: list[tuple[F, F]]) -> F:
    for left, right in closed_union(segments):
        if left <= original.RHO_TOP <= right:
            return left
    return original.RHO_TOP


class ContinuationSession(original.AffineSession):
    """Reuse original pricing/checkpoint hooks; only the finite plan/union changes."""

    def __init__(self, args):
        self.args, self.started = args, time.monotonic()
        if args.output.exists():
            raise FileExistsError('Choose a NEW output path; prior results are read-only.')
        assert args.output.parent.exists() and args.seed_json.is_file()
        assert args.output.resolve() != args.seed_json.resolve()
        if args.resume_from:
            assert args.output.resolve() != args.resume_from.resolve()
            self.record = json.loads(args.resume_from.read_text(encoding='utf-8'))
            assert self.record['format'] == FORMAT and self.record['model'] == engine.MODEL
            assert self.record['settings'] == self.settings()
        else:
            self.record = {'format': FORMAT, 'date': '2026-10-30', 'model': engine.MODEL,
                           'settings': self.settings(), 'rounds': [], 'completed_prices': {}, 'price_attempts': [],
                           'new_price_attempts': 0, 'active_price_key': None, 'active_price_attempt_index': None,
                           'terminal_failure': False, 'stop_reason': None,
                           'genuine_CDF_profile_endpoint_Lean_proved': True,
                           'numerical_interval_to_profile_Lean_proved': False, 'formal_lean_numerical_theorem': False,
                           'actual_rho_equals_one_assumed': False, 'CF_prices_assume_hprev': False,
                           'new_Gaussian_mask_assumed': False, 'old_n31_actual_cap_prices_used': False,
                           'all_n_classical_formula_claimed': False, 'original_guess_certified': False}
        self.engines, self.allowed = {}, {}
        self.load_seed()
        self.validate_state()
        index = self.record['active_price_attempt_index']
        if index is not None:
            if self.record['price_attempts'][index]['status'] == 'in-progress':
                self.record['price_attempts'][index]['status'] = 'interrupted'
            self.record['active_price_attempt_index'] = None
        self.record['active_price_key'] = None
        self.save()

    @staticmethod
    def settings() -> dict:
        return {**original.AffineSession.settings(), 'nu_nodes': [[str(a), str(b)]
                for a, b in zip(NU_ENDPOINTS, NU_ENDPOINTS[1:])],
                'first_new_upper_anchor': str(ANCHOR), 'old_frontier': str(OLD_FRONTIER),
                'max_rounds': MAX_NEW_ROUNDS, 'max_new_price_attempts': MAX_NEW_PRICES,
                'first_new_prices': 2, 'subsequent_prices_per_round': 5,
                'coverage_rule': 'exact union of all old and new certified closed moment segments'}

    def register_round(self, U: F):
        context, A, nodes = fine_parameters(U)
        if context not in self.engines:
            self.engines[context] = engine.UpperMomentSineEvaluator(
                A, self.record['completed_prices'], on_change=self.save, on_part=self.save_part, context=context)
        for nu in NU_ENDPOINTS:
            self.allowed[engine.price_key(nu, A, context=context)] = (context, A, nu)
        return context, A, nodes

    def load_seed(self):
        old = json.loads(self.args.seed_json.read_text(encoding='utf-8'))
        assert old['format'] == original.FORMAT and old['model'] == engine.MODEL
        assert old['settings'] == original.AffineSession.settings()
        assert len(old['rounds']) == 8 and old['new_price_attempts'] == len(old['completed_prices']) == 24
        assert all(row['status'] == 'completed' for row in old['rounds'])
        assert F(old['rounds'][-1]['U']) == ANCHOR and F(old['rounds'][-1]['L']) == OLD_FRONTIER
        assert old['unresolved_rho_domain'] == [[str(original.RHO_BOTTOM), str(OLD_FRONTIER)]]
        for row in old['rounds']:
            U = F(row['U'])
            context, A, _ = self.register_round(U)
            assert row['context'] == engine.fixed_parameters(context=context) and row['A'] == str(A)
        for key, value in old['completed_prices'].items():
            context, A, nu = self.allowed[key]
            assert key == engine.price_key(nu, A, context=context)
            assert value['parameters'] == engine.physical_parameters(nu, A, context=context)
            self.engines[context].validate(value)
            if key in self.record['completed_prices']:
                assert self.record['completed_prices'][key] == value
            else:
                self.record['completed_prices'][key] = deepcopy(value)
        source_segments = []
        for row in old['rounds']:
            context, A, coarse = original.round_parameters(F(row['U']))
            assert row['nodes'] == [node.record(context=context) for node in coarse]
            assert len(row['proved_nodes']) == 2
            assert {a['name'] for a in row['proved_nodes']} == {node.name for node in coarse}
            for attempt in row['proved_nodes']:
                node = next(node for node in coarse if node.name == attempt['name'])
                self.validate_joint(attempt, context, node)
            B = max(F(int(a['joint_upper']['upper_numerator']), int(a['joint_upper']['denominator']))
                    for a in row['proved_nodes'])
            lower, _ = original.lower_from_B(B)
            assert F(row['L']) == lower < context.U and B < context.target
            assert row['B_upper'] == engine.record_fraction(B)
            source_segments.append({'rho_lower': str(lower), 'rho_upper': str(context.U), 'B_upper': row['B_upper']})
        assert source_segments == old['covered_closed_rho_segments']
        assert frontier([(F(s['rho_lower']), F(s['rho_upper'])) for s in source_segments]) == OLD_FRONTIER
        anchor_keys = [engine.price_key(nu, F(3, 5)*ANCHOR, context=fine_parameters(ANCHOR)[0])
                       for nu in (F(31), F(155, 4), F(46))]
        assert all(key in old['completed_prices'] for key in anchor_keys)
        self.record.update({'read_only_source': self.args.seed_json.name, 'seed_rounds': deepcopy(old['rounds']),
                            'seed_closed_segments': deepcopy(source_segments), 'seed_price_keys': list(old['completed_prices']),
                            'source_stop_reason_preserved': old['stop_reason'], 'anchor_three_literal_price_keys': anchor_keys})

    def segments(self, extra=None) -> list[tuple[F, F]]:
        segments = [(F(s['rho_lower']), F(s['rho_upper'])) for s in self.record['seed_closed_segments']]
        segments.extend((F(row['L']), F(row['U'])) for row in self.record['rounds']
                        if row.get('affine_segment_certified', False))
        if extra is not None:
            segments.append(extra)
        return segments

    def validate_state(self):
        assert len(self.record['rounds']) <= MAX_NEW_ROUNDS
        before_segments = [(F(s['rho_lower']), F(s['rho_upper'])) for s in self.record['seed_closed_segments']]
        next_U = ANCHOR
        for index, row in enumerate(self.record['rounds']):
            U = F(row['U'])
            assert U == next_U and F(row['frontier_before']) == frontier(before_segments)
            context, A, nodes = self.register_round(U)
            assert row['context'] == engine.fixed_parameters(context=context) and row['A'] == str(A)
            assert row['nodes'] == [node.record(context=context) for node in nodes]
            assert len({a['name'] for a in row['proved_nodes']}) == len(row['proved_nodes'])
            for attempt in row['proved_nodes']:
                self.validate_joint(attempt, context, next(node for node in nodes if node.name == attempt['name']))
            if row.get('affine_segment_certified', False):
                assert len(row['proved_nodes']) == 4
                B = max(F(int(a['joint_upper']['upper_numerator']), int(a['joint_upper']['denominator']))
                        for a in row['proved_nodes'])
                lower, _ = original.lower_from_B(B)
                assert F(row['L']) == lower <= U and B < context.target
                before_segments.append((lower, U))
                if row['status'] == 'completed':
                    assert frontier(before_segments) < F(row['frontier_before'])
                    next_U = lower
            if row['status'] != 'completed':
                assert index == len(self.record['rounds'])-1
        for key, value in self.record['completed_prices'].items():
            context, A, nu = self.allowed[key]
            self.engines[context].validate(value)
            assert value['parameters'] == engine.physical_parameters(nu, A, context=context)
        assert len(self.record['price_attempts']) == self.record['new_price_attempts'] <= MAX_NEW_PRICES

    def save(self):
        merged = closed_union(self.segments())
        self.record['closed_union_rho_segments'] = [[str(a), str(b)] for a, b in merged]
        self.record['frontier_connected_to_rho0'] = str(frontier(self.segments()))
        gaps, cursor = [], original.RHO_BOTTOM
        for left, right in merged:
            if cursor < left:
                gaps.append([str(cursor), str(left)])
            cursor = max(cursor, right)
        if cursor < original.RHO_TOP:
            gaps.append([str(cursor), str(original.RHO_TOP)])
        self.record['unresolved_rho_domain'] = gaps
        self.record['finite31_through46_affine_T_envelope_arithmetic_certified'] = any(
            left <= original.RHO_BOTTOM and right >= original.RHO_TOP for left, right in merged)
        self.record['current_invocation_elapsed_seconds_metadata'] = time.monotonic()-self.started
        original.atomic_save(self.args.output, self.record)

    def evaluate(self, context, A: F, nu: F):
        key = engine.price_key(nu, A, context=context)
        if key not in self.record['completed_prices'] and self.record['new_price_attempts'] >= MAX_NEW_PRICES:
            raise RuntimeError('Cumulative SEVENTEEN continuation-price attempt limit reached.')
        # Original mutation/checkpoint logic is reused; this tighter guard precedes
        # its old 24-price guard without changing the original module's globals.
        return super().evaluate(context, A, nu)

    def run(self):
        if self.record['terminal_failure']:
            return
        for _ in range(MAX_NEW_ROUNDS):
            rows = self.record['rounds']
            if rows and rows[-1]['status'] != 'completed':
                row, U = rows[-1], F(rows[-1]['U'])
            else:
                before = frontier(self.segments())
                if before == original.RHO_BOTTOM:
                    return
                if len(rows) >= MAX_NEW_ROUNDS:
                    self.stop('Fixed four-new-round limit reached; unresolved domain preserved.')
                    return
                U = F(rows[-1]['L']) if rows else ANCHOR
                context, A, nodes = self.register_round(U)
                row = {'index': len(rows)+1, 'U': str(U), 'A': str(A), 'frontier_before': str(before),
                       'context': engine.fixed_parameters(context=context),
                       'nodes': [node.record(context=context) for node in nodes],
                       'status': 'in-progress', 'node_attempts': [], 'proved_nodes': [],
                       'affine_segment_certified': False}
                rows.append(row)
                self.save()
            context, A, nodes = self.register_round(U)
            for node in nodes:
                if any(a['name'] == node.name for a in row['proved_nodes']):
                    continue
                keys = [engine.price_key(nu, A, context=context) for nu in (node.left, node.right)]
                attempt = {'name': node.name, 'node': node.record(context=context), 'status': 'in-progress',
                           'endpoint_keys': keys, 'obtained_endpoint_keys': []}
                row['node_attempts'].append(attempt)
                self.save()
                values = []
                for nu, key in zip((node.left, node.right), keys):
                    try:
                        value = self.evaluate(context, A, nu)
                    except Exception as error:
                        self.stop('Endpoint arithmetic or continuation budget failed; no automatic retry.',
                                  row=row, attempt=attempt, failed_price_key=key,
                                  error_kind=type(error).__name__, error_message=str(error))
                        return
                    attempt['obtained_endpoint_keys'].append(key)
                    values.append(original.absolute_B(value))
                    if values[-1] >= context.target:
                        self.stop('Point B is not strict below the unchanged progress cap.', row=row,
                                  attempt=attempt, failed_price_key=key)
                        return
                    self.save()
                theta = engine.RMAX*(node.right-node.left)**2/(8*node.left**2)
                assert 0 <= theta < 1
                factor, joint = 1/(1-theta), max(values)/(1-theta)
                attempt.update({'theta': str(theta), 'factor': str(factor),
                                'joint_upper': engine.record_fraction(joint), 'strict_joint': joint < context.target})
                if joint >= context.target:
                    self.stop('Fine joint B is not strict below the unchanged progress cap.', row=row, attempt=attempt)
                    return
                attempt['status'] = 'passed'
                row['proved_nodes'].append(attempt)
                self.save()
            B = max(F(int(a['joint_upper']['upper_numerator']), int(a['joint_upper']['denominator']))
                    for a in row['proved_nodes'])
            lower, threshold = original.lower_from_B(B)
            row.update({'B_upper': engine.record_fraction(B), 'L': str(lower),
                        'unrounded_lower_threshold': str(threshold),
                        'affine_segment_certified': lower <= U,
                        'all_three_affine_budgets_paid': all(B <= a*lower+b for a, b in original.BUDGETS)})
            after = frontier(self.segments())
            row['frontier_after_candidate'] = str(after)
            if lower > U or after >= F(row['frontier_before']):
                self.stop('No true union-frontier progress; all valid overlapping segments retained.', row=row)
                return
            row['status'] = 'completed'
            self.save()
            print(json.dumps({'new_round': row['index'], 'rho_closed_segment': [str(lower), str(U)],
                              'frontier': str(after), 'B_upper': row['B_upper']['decimal_upper']}), flush=True)
        if self.record['unresolved_rho_domain']:
            self.stop('Fixed four-new-round limit reached; unresolved domain preserved.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--continue-cover', action='store_true', help='Explicitly run only this fixed fine-nu continuation.')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--seed-json', type=Path, default=Path(__file__).with_name('upper_moment_finite_affine_cover.json'))
    parser.add_argument('--resume-from', type=Path, help='Matching continuation checkpoint; output must be new.')
    args = parser.parse_args()
    if not args.continue_cover:
        parser.error('Use --continue-cover explicitly after source review; no prices by default.')
    engine.scalar.base.pin_two_cpus()
    session = ContinuationSession(args)
    session.run()
    print(json.dumps({'finite31_through46_affine_T_envelope_arithmetic_certified':
                      session.record['finite31_through46_affine_T_envelope_arithmetic_certified'],
                      'new_price_attempts': session.record['new_price_attempts'], 'stop_reason': session.record['stop_reason'],
                      'closed_union_rho_segments': session.record['closed_union_rho_segments'],
                      'unresolved_rho_domain': session.record['unresolved_rho_domain'],
                      'formal_lean_numerical_theorem': False, 'original_guess_certified': False}), flush=True)


if __name__ == '__main__':
    main()
