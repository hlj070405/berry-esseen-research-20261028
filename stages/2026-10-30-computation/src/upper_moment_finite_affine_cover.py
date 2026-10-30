"""2026-10-30: finite n31..46 affine T cover; PREPARED, no automatic prices.

Only --cover runs this fixed rule on actual rho in [8/5,7361/4000].
At each upper moment U, context sigma=U,rhoLower=1 uses the unchanged global
sine evaluator.  rhoLower=1 is ONLY the output scale making its number
B=sqrt(nu)*absolute_Delta=U*normalized_profile.  It is not actual rho=1,
and no ratio_le_endpoints theorem is inverted to obtain B.  Use the genuine
CDF/profile endpoint theorem, then sqrt(actual n)*betaScale U n=U.

Fix A=3U/5 (raw summand cutoff u0=.6),V4,res2048,Gamma(U) and full G/W.
The two fixed nu nodes are [31,155/4] and [155/4,46], with rmax3/2.
Their shared midpoint has the SAME A/context and is priced once: THREE
new prices per U.  No old n31 B6 actual-error-cap price is imported or used.
The evaluator advances the global coarse profile, never a Taylor/triangle
intersection.  All upper-moment parameters remain frozen within both nodes.

For exact affine budgets (.469,0),(.3322,.1425138),(.3031,.1958026), the
progress cap is their MIN at U.  Every point and joint must be strictly below
that cap.  B=max(two joints), then
 L=max(8/5,ceil_1e-6(max(B/.469,(B-.1425138)/.3322,(B-.1958026)/.3031))).
Exact B<=a_j*L+b_j for all three budgets pays the WHOLE CLOSED [L,U].
Only after all prices are frozen is L derived; A/Gamma/context are never
recomputed from L.  Next U=L, until 1.6, at most EIGHT rounds/TWENTY-FOUR
new attempts cumulatively.  This is one analytic descent, not a parameter grid.

First arithmetic/point/joint/progress failure stops with all complete prices,
complete nodes and the entire unresolved rho domain retained.  Completed
prices are atomically durable before scoring; resume needs a NEW output path
and does not repeat matching completed prices.  No per-cell snapshots.
Analytic genuine-CDF/profile/endpoint Lean statements have passed standard
build and independent reading.  External interval arithmetic is not a Lean
numerical theorem.  The only goal here is this finite T moment envelope;
all-n classical formula, Gaussian-mask collection and original guess remain
unclaimed.  Only elapsed metadata is floating point.  No frozen source,
old result, Lean file or summary document is changed.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
import os
from pathlib import Path
import time

import upper_moment_sine_nodes as engine


FORMAT = 'upper-moment-finite31-46-affine-cover-v1'
RHO_BOTTOM, RHO_TOP = F(8, 5), F(7361, 4000)
MAX_ROUNDS, MAX_NEW_PRICES = 8, 24
BUDGETS = ((F(469, 1000), F(0)),
           (F(1661, 5000), F(712569, 5000000)),
           (F(3031, 10000), F(979013, 5000000)))
NU_NODES = ((F(31), F(155, 4)), (F(155, 4), F(46)))


def round_parameters(U: F):
    assert RHO_BOTTOM < U <= RHO_TOP
    target = min(a*U+b for a, b in BUDGETS)
    context = engine.UpperMomentContext(U=U, sigma=U, rhoLower=F(1), target=target)
    A = F(3, 5)*U
    nodes = tuple(engine.SpectralNode(f'nu-{a}-to-{b}', a, b, A) for a, b in NU_NODES)
    return context, A, nodes


def absolute_B(result: dict) -> F:
    """Obtain U*profile directly from absolute Delta, never from a ratio theorem."""
    p, delta = result['parameters'], result['delta_upper']
    assert p['rhoLower'] == '1' and delta['denominator'] == str(engine.S)
    numerator = int(delta['upper_numerator'])
    upper = (engine.rat(F(p['nu'])).sqrt()*engine.I(numerator, numerator)).upper()
    assert engine.scalar.base.rational_text(upper) == result['ratio_upper']
    return F(upper.hi, engine.S)


def lower_from_B(B: F) -> tuple[F, F]:
    threshold = max((B-b)/a for a, b in BUDGETS)
    micro_ceiling = -((-threshold.numerator*1000000)//threshold.denominator)
    lower = max(RHO_BOTTOM, F(micro_ceiling, 1000000))
    assert all(B <= a*lower+b for a, b in BUDGETS)
    return lower, threshold


def atomic_save(path: Path, record: dict):
    temp = path.with_name(path.name+'.tmp')
    with temp.open('w', encoding='utf-8', newline='\n') as handle:
        json.dump(record, handle, indent=2)
        handle.write('\n')
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temp, path)


class AffineSession:
    def __init__(self, args):
        self.args, self.started = args, time.monotonic()
        if args.output.exists():
            raise FileExistsError('Choose a NEW output path; previous results are read-only.')
        assert args.output.parent.exists()
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
                           'analytic_Lean_theorem': 'BerryEsseen.UpperMomentSpectrumPrice.normalized_actual_cdf_le_endpoints',
                           'ratio_endpoint_theorem_used_to_derive_B': False, 'actual_rho_equals_one_assumed': False,
                           'numerical_interval_to_profile_Lean_proved': False, 'formal_lean_numerical_theorem': False,
                           'old_n31_B6_actual_cap_prices_used': False, 'Gaussian_masks_collected': False,
                           'all_n_classical_formula_claimed': False, 'original_guess_certified': False}
        self.engines = {}
        self.allowed = {}
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
        return {'actual_n_domain': [31, 46], 'rho_domain': [str(RHO_BOTTOM), str(RHO_TOP)],
                'affine_budgets': [[str(a), str(b)] for a, b in BUDGETS],
                'nu_nodes': [[str(a), str(b)] for a, b in NU_NODES], 'A_rule': '3*U/5',
                'sigma_rule': 'U', 'output_rhoLower': '1', 'output_quantity': 'sqrt(nu)*absolute_Delta = U*profile',
                'V': str(engine.V), 'resolution': engine.RESOLUTION, 'exp_method': engine.EXP_METHOD,
                'rmax': str(engine.RMAX), 'max_rounds': MAX_ROUNDS, 'max_new_price_attempts': MAX_NEW_PRICES,
                'lower_rounding': 'ceiling to 1e-6', 'automatic_parameter_search': False}

    def register_round(self, U: F):
        context, A, nodes = round_parameters(U)
        if context not in self.engines:
            self.engines[context] = engine.UpperMomentSineEvaluator(
                A, self.record['completed_prices'], on_change=self.save, on_part=self.save_part, context=context)
        for nu in (F(31), F(155, 4), F(46)):
            self.allowed[engine.price_key(nu, A, context=context)] = (context, A, nu)
        return context, A, nodes

    def validate_state(self):
        cursor = RHO_TOP
        assert len(self.record['rounds']) <= MAX_ROUNDS
        for index, row in enumerate(self.record['rounds']):
            U = F(row['U'])
            assert U == cursor
            context, A, nodes = self.register_round(U)
            assert row['context'] == engine.fixed_parameters(context=context) and row['A'] == str(A)
            assert row['nodes'] == [node.record(context=context) for node in nodes]
            for attempt in row['proved_nodes']:
                node = next(node for node in nodes if node.name == attempt['name'])
                self.validate_joint(attempt, context, node)
            if row['status'] == 'completed':
                assert len(row['proved_nodes']) == 2
                B = max(F(int(a['joint_upper']['upper_numerator']), int(a['joint_upper']['denominator']))
                        for a in row['proved_nodes'])
                lower, _ = lower_from_B(B)
                assert F(row['L']) == lower < U and B < context.target
                cursor = lower
            else:
                assert index == len(self.record['rounds'])-1
        for key, result in self.record['completed_prices'].items():
            context, A, nu = self.allowed[key]
            self.engines[context].validate(result)
            assert result['parameters'] == engine.physical_parameters(nu, A, context=context)
        assert len(self.record['price_attempts']) == self.record['new_price_attempts'] <= MAX_NEW_PRICES

    def validate_joint(self, attempt: dict, context, node):
        assert attempt['node'] == node.record(context=context) and attempt['status'] == 'passed'
        keys = [engine.price_key(nu, node.A, context=context) for nu in (node.left, node.right)]
        assert attempt['endpoint_keys'] == keys
        theta = engine.RMAX*(node.right-node.left)**2/(8*node.left**2)
        joint = max(absolute_B(self.record['completed_prices'][key]) for key in keys)/(1-theta)
        assert F(attempt['theta']) == theta and F(attempt['factor']) == 1/(1-theta)
        p = attempt['joint_upper']
        assert F(int(p['upper_numerator']), int(p['denominator'])) == joint < context.target

    def save(self):
        completed = [row for row in self.record['rounds'] if row['status'] == 'completed']
        upper = F(completed[-1]['L']) if completed else RHO_TOP
        self.record['covered_closed_rho_segments'] = [
            {'rho_lower': row['L'], 'rho_upper': row['U'], 'B_upper': row['B_upper']} for row in completed]
        self.record['unresolved_rho_domain'] = [[str(RHO_BOTTOM), str(upper)]] if upper > RHO_BOTTOM else []
        self.record['finite31_through46_affine_T_envelope_arithmetic_certified'] = upper == RHO_BOTTOM
        self.record['current_invocation_elapsed_seconds_metadata'] = time.monotonic()-self.started
        atomic_save(self.args.output, self.record)

    def save_part(self, key: str, name: str, part: dict, next_stage: str):
        index = self.record['active_price_attempt_index']
        assert index is not None and self.record['price_attempts'][index]['key'] == key
        attempt = self.record['price_attempts'][index]
        attempt['completed_absolute_terms'][name] = part
        attempt['active_stage'] = next_stage
        self.save()

    def evaluate(self, context, A: F, nu: F):
        key, evaluator = engine.price_key(nu, A, context=context), self.engines[context]
        if key in self.record['completed_prices']:
            return evaluator.evaluate(nu)
        if self.record['new_price_attempts'] >= MAX_NEW_PRICES:
            raise RuntimeError('Cumulative TWENTY-FOUR new-price attempt limit reached.')
        attempt = {'key': key, 'parameters': engine.physical_parameters(nu, A, context=context),
                   'status': 'in-progress', 'active_stage': 'first-ODE', 'completed_absolute_terms': {}}
        self.record['price_attempts'].append(attempt)
        self.record['new_price_attempts'] += 1
        self.record['active_price_key'] = key
        self.record['active_price_attempt_index'] = len(self.record['price_attempts'])-1
        self.save()
        try:
            result = evaluator.evaluate(nu)
        except BaseException as error:
            attempt.update({'status': 'interrupted' if isinstance(error, KeyboardInterrupt) else 'failed',
                            'error_kind': type(error).__name__, 'error_message': str(error)})
            self.record['active_price_key'] = self.record['active_price_attempt_index'] = None
            self.save()
            raise
        attempt.update({'status': 'completed', 'active_stage': None})
        self.record['active_price_key'] = self.record['active_price_attempt_index'] = None
        self.save()
        return result

    def stop(self, reason: str, *, row=None, attempt=None, **details):
        self.record.update({'terminal_failure': True, 'stop_reason': reason})
        if row is not None:
            row.update({'status': 'failed', 'failure': reason, **details})
        if attempt is not None:
            attempt.update({'status': 'failed', 'failure': reason, **details})
        self.save()

    def run(self):
        if self.record['terminal_failure']:
            return
        for _ in range(MAX_ROUNDS):
            rows = self.record['rounds']
            if rows and rows[-1]['status'] != 'completed':
                row, U = rows[-1], F(rows[-1]['U'])
            else:
                U = F(rows[-1]['L']) if rows else RHO_TOP
                if U == RHO_BOTTOM:
                    return
                if len(rows) >= MAX_ROUNDS:
                    self.stop('Fixed eight-round limit reached; unresolved domain preserved.')
                    return
                context, A, nodes = self.register_round(U)
                row = {'index': len(rows)+1, 'U': str(U), 'A': str(A),
                       'context': engine.fixed_parameters(context=context),
                       'nodes': [node.record(context=context) for node in nodes],
                       'status': 'in-progress', 'node_attempts': [], 'proved_nodes': []}
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
                        result = self.evaluate(context, A, nu)
                    except Exception as error:
                        self.stop('Endpoint arithmetic or cumulative budget failed; no automatic retry.',
                                  row=row, attempt=attempt, failed_price_key=key,
                                  error_kind=type(error).__name__, error_message=str(error))
                        return
                    attempt['obtained_endpoint_keys'].append(key)
                    values.append(absolute_B(result))
                    if values[-1] >= context.target:
                        self.stop('Point B is not strict below the fixed progress cap.', row=row, attempt=attempt,
                                  failed_price_key=key)
                        return
                    self.save()
                theta = engine.RMAX*(node.right-node.left)**2/(8*node.left**2)
                assert 0 <= theta < 1
                factor, joint = 1/(1-theta), max(values)/(1-theta)
                attempt.update({'theta': str(theta), 'factor': str(factor),
                                'joint_upper': engine.record_fraction(joint), 'strict_joint': joint < context.target})
                if joint >= context.target:
                    self.stop('Joint B is not strict below the fixed progress cap.', row=row, attempt=attempt)
                    return
                attempt['status'] = 'passed'
                row['proved_nodes'].append(attempt)
                self.save()
            B = max(F(int(a['joint_upper']['upper_numerator']), int(a['joint_upper']['denominator']))
                    for a in row['proved_nodes'])
            lower, threshold = lower_from_B(B)
            row.update({'B_upper': engine.record_fraction(B), 'unrounded_lower_threshold': str(threshold),
                        'L': str(lower), 'all_three_affine_budgets_paid': all(B <= a*lower+b for a, b in BUDGETS)})
            if lower >= U:
                self.stop('Rounded lower L>=U; no progress and no cutoff change.', row=row)
                return
            row['status'] = 'completed'
            self.save()
            print(json.dumps({'round': row['index'], 'rho_closed_segment': [str(lower), str(U)],
                              'B_upper': row['B_upper']['decimal_upper'], 'all_three_affine_budgets_paid': True}), flush=True)
        if self.record['unresolved_rho_domain']:
            self.stop('Fixed eight-round limit reached; unresolved domain preserved.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cover', action='store_true', help='Explicitly run only this fixed finite31..46 affine descent.')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--resume-from', type=Path, help='Matching checkpoint; output must be new.')
    args = parser.parse_args()
    if not args.cover:
        parser.error('Use --cover explicitly after source review; no prices by default.')
    engine.scalar.base.pin_two_cpus()
    session = AffineSession(args)
    session.run()
    print(json.dumps({'finite31_through46_affine_T_envelope_arithmetic_certified':
                      session.record['finite31_through46_affine_T_envelope_arithmetic_certified'],
                      'new_price_attempts': session.record['new_price_attempts'], 'stop_reason': session.record['stop_reason'],
                      'unresolved_rho_domain': session.record['unresolved_rho_domain'],
                      'all_n_classical_formula_claimed': False, 'original_guess_certified': False}), flush=True)


if __name__ == '__main__':
    main()
