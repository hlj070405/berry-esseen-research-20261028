"""2026-10-30: fixed INITIAL47 cells i20/i21/i22; PREPARED, no auto-run.

Only --remaining runs prices, using the existing context/evaluator unchanged.
For r_i=1+(3361/4000)*i/24 use U=sigma=r_(i+1),L=r_i and the exact target
(1661/5000)*(1+(429/1000)/r_i).  V4,res2048, full W and fixed G per context.
The GaussianInitialMask source retains its full-domain hprev premise; these
standalone CF prices do not assume hprev or collect any Gaussian masks.

Only these finite residual actual-index domains are priced:
 i20: n47, a single deterministic POINT with no chord or fake a<b node;
 i21: n47..65, exactly TWO nodes; i22: n47..100, exactly FOUR nodes.
For nodes use b=min(5*a/4,M) from a47.  Each point/node uses the ONE cutoff
A=floor_.001(3*U/sqrt(a)), from the existing interval lower endpoint.
All endpoint parameters U,sigma,GammaUpper,L,A,V,res are bound in the key.
There are no other rho/index/cutoff candidates or adaptive refinements.

The point needs only ratio<target.  Nodes use the same p3/2 exact chord
factor.  At most THIRTEEN cumulative new prices (1+4+8), including interrupted
attempts.  Completed prices are atomic/durable before scoring.  First failure
stops the whole sequence and preserves all three cases' remaining domains.
Resume requires a NEW output path and reuses only matching completed prices.

Analytic upper-moment CF/CDF/profile and endpoint statements have passed the
standard Lean build and independent review.  These external numerical bounds
are not Lean numerical theorems.  Even if all three cells pass, overall
INITIAL47 stays FALSE until case23 and all Gaussian masks are collected in a
separate task.  No source/result/Lean file is modified.  No per-cell snapshots,
extra reports or integrator copies.  Only elapsed metadata is floating point.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
import os
from pathlib import Path
import time

import upper_moment_sine_nodes as engine


FORMAT = 'upper-moment-initial47-i20-i22-v1'
MAX_NEW_PRICES = 13


@dataclass(frozen=True)
class Case:
    i: int
    maximum: int
    context: engine.UpperMomentContext

    def record(self) -> dict:
        fixed = engine.fixed_parameters(context=self.context)
        fixed['max_new_price_attempts'] = MAX_NEW_PRICES
        return {'i': self.i, 'actual_n_domain': [47, self.maximum],
                'rho_closed_box': [str(self.context.rhoLower), str(self.context.U)],
                'target': str(self.context.target), 'fixed_spectrum_parameters': fixed}


def cases() -> tuple[Case, ...]:
    result = []
    for i, maximum in ((20, 47), (21, 65), (22, 100)):
        lower = 1+F(3361, 4000)*F(i, 24)
        upper = 1+F(3361, 4000)*F(i+1, 24)
        target = F(1661, 5000)*(1+F(429, 1000)/lower)
        context = engine.UpperMomentContext(U=upper, sigma=upper, rhoLower=lower, target=target)
        result.append(Case(i, maximum, context))
    return tuple(result)


def cutoff_at_left(context: engine.UpperMomentContext, left: F) -> F:
    cutoff = 3*engine.rat(context.U)/engine.rat(left).sqrt()
    A = F((1000*cutoff.lo)//engine.S, 1000)
    assert 0 < A < engine.V and A*A*left <= 9*context.U**2
    return A


@dataclass(frozen=True)
class Entry:
    name: str
    case: Case
    left: F
    A: F
    right: F | None = None

    def endpoints(self) -> tuple[F, ...]:
        return (self.left,) if self.right is None else (self.left, self.right)

    def record(self) -> dict:
        base = {'name': self.name, 'i': self.case.i, 'A': str(self.A),
                'context': self.case.record()['fixed_spectrum_parameters']}
        if self.right is None:
            return {**base, 'kind': 'point', 'nu': str(self.left)}
        theta = engine.RMAX*(self.right-self.left)**2/(8*self.left**2)
        assert self.left < self.right and 0 <= theta < 1
        assert self.A*self.A*self.right/self.case.context.sigma**2 < 64
        return {**base, 'kind': 'node', 'nu_left': str(self.left), 'nu_right': str(self.right),
                'rmax': str(engine.RMAX), 'theta': str(theta), 'factor': str(1/(1-theta))}


def prepared_entries(case_list: tuple[Case, ...]) -> tuple[Entry, ...]:
    entries = []
    for case, expected_nodes in zip(case_list, (0, 2, 4)):
        left = F(47)
        if expected_nodes == 0:
            assert case.maximum == 47
            entries.append(Entry('i20-nu47-point', case, left, cutoff_at_left(case.context, left)))
            continue
        for index in range(1, expected_nodes+1):
            assert left < case.maximum
            right = min(F(5, 4)*left, F(case.maximum))
            entries.append(Entry(f'i{case.i}-node-{index:02d}', case, left,
                                 cutoff_at_left(case.context, left), right))
            left = right
        assert left == case.maximum
    assert len(entries) == 7 and sum(len(entry.endpoints()) for entry in entries) == MAX_NEW_PRICES
    return tuple(entries)


def atomic_save(path: Path, record: dict):
    temp = path.with_name(path.name+'.tmp')
    with temp.open('w', encoding='utf-8', newline='\n') as handle:
        json.dump(record, handle, indent=2)
        handle.write('\n')
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temp, path)


class RemainingSession:
    def __init__(self, args):
        self.args, self.started = args, time.monotonic()
        self.cases = cases()
        self.entries = prepared_entries(self.cases)
        self.by_name = {entry.name: entry for entry in self.entries}
        self.allowed = {engine.price_key(nu, entry.A, context=entry.case.context): (entry, nu)
                        for entry in self.entries for nu in entry.endpoints()}
        assert len(self.allowed) == MAX_NEW_PRICES
        if args.output.exists():
            raise FileExistsError('Choose a NEW output path; previous results are read-only.')
        assert args.output.parent.exists()
        if args.resume_from:
            assert args.output.resolve() != args.resume_from.resolve()
            self.record = json.loads(args.resume_from.read_text(encoding='utf-8'))
            assert self.record['format'] == FORMAT and self.record['model'] == engine.MODEL
            assert self.record['cases'] == [case.record() for case in self.cases]
            assert self.record['plans'] == [entry.record() for entry in self.entries]
        else:
            self.record = {'format': FORMAT, 'date': '2026-10-30', 'model': engine.MODEL,
                           'cases': [case.record() for case in self.cases],
                           'plans': [entry.record() for entry in self.entries], 'max_new_price_attempts': MAX_NEW_PRICES,
                           'completed_prices': {}, 'price_attempts': [], 'entry_attempts': [], 'proved_entries': [],
                           'new_price_attempts': 0, 'active_price_key': None, 'active_price_attempt_index': None,
                           'active_entry_index': None, 'terminal_failure': False, 'stop_reason': None,
                           'analytic_CF_CDF_profile_endpoint_Lean_proved': True,
                           'analytic_Lean_source': 'BerryEsseen.UpperMomentSpectrumPrice',
                           'numerical_interval_to_profile_Lean_proved': False, 'formal_lean_numerical_theorem': False,
                           'Gaussian_mask_source': 'BerryEsseen.GaussianInitialMask',
                           'Gaussian_mask_requires_full_domain_hprev': True, 'CF_prices_assume_hprev': False,
                           'Gaussian_masks_collected': False, 'case23_collected': False,
                           'entire_INITIAL47_certified': False, 'complete_classical_formula_claimed': False,
                           'noninteger_iid_sum_claimed': False}
        self.engines = {(entry.case.context, entry.A): engine.UpperMomentSineEvaluator(
            entry.A, self.record['completed_prices'], context=entry.case.context) for entry in self.entries}
        self.validate_state()
        for pointer, collection in (('active_price_attempt_index', 'price_attempts'),
                                    ('active_entry_index', 'entry_attempts')):
            index = self.record[pointer]
            if index is not None:
                if self.record[collection][index]['status'] == 'in-progress':
                    self.record[collection][index]['status'] = 'interrupted'
                self.record[pointer] = None
        self.record['active_price_key'] = None
        for evaluator in self.engines.values():
            evaluator.on_change, evaluator.on_part = self.save, self.save_part
        self.save()

    def validate_state(self):
        for key, value in self.record['completed_prices'].items():
            entry, nu = self.allowed[key]
            self.engines[(entry.case.context, entry.A)].validate(value)
            assert value['parameters'] == engine.physical_parameters(nu, entry.A, context=entry.case.context)
        assert len(self.record['price_attempts']) == self.record['new_price_attempts'] <= MAX_NEW_PRICES
        for attempt in self.record['price_attempts']:
            entry, nu = self.allowed[attempt['key']]
            assert attempt['parameters'] == engine.physical_parameters(nu, entry.A, context=entry.case.context)
        seen = set()
        for attempt in self.record['proved_entries']:
            entry = self.by_name[attempt['name']]
            assert entry.name not in seen and attempt['entry'] == entry.record() and attempt['status'] == 'passed'
            seen.add(entry.name)
            keys = [engine.price_key(nu, entry.A, context=entry.case.context) for nu in entry.endpoints()]
            assert attempt['endpoint_keys'] == keys
            comparison = max(engine.score(self.record['completed_prices'][key]) for key in keys)
            if entry.right is not None:
                theta = engine.RMAX*(entry.right-entry.left)**2/(8*entry.left**2)
                assert F(attempt['theta']) == theta and F(attempt['factor']) == 1/(1-theta)
                comparison /= 1-theta
            p = attempt['comparison_upper']
            assert F(int(p['upper_numerator']), int(p['denominator'])) == comparison < entry.case.context.target

    def save(self):
        passed = {attempt['name'] for attempt in self.record['proved_entries']}
        remaining = {str(case.i): [entry.record() for entry in self.entries
                                   if entry.case.i == case.i and entry.name not in passed] for case in self.cases}
        certified = {}
        for case in self.cases:
            selected = [entry for entry in self.entries if entry.case.i == case.i]
            if case.maximum == 47:
                certified[str(case.i)] = len(selected) == 1 and selected[0].right is None and selected[0].name in passed
            else:
                cursor = F(47)
                for entry in selected:
                    if entry.name not in passed or entry.left != cursor:
                        break
                    cursor = entry.right
                certified[str(case.i)] = not remaining[str(case.i)] and cursor == case.maximum
        self.record['remaining_by_case'] = remaining
        self.record['case_arithmetic_certified'] = certified
        self.record['three_remaining_cells_arithmetic_certified'] = all(certified.values())
        self.record['current_invocation_elapsed_seconds_metadata'] = time.monotonic()-self.started
        atomic_save(self.args.output, self.record)

    def save_part(self, key: str, name: str, part: dict, next_stage: str):
        index = self.record['active_price_attempt_index']
        assert index is not None and self.record['price_attempts'][index]['key'] == key
        attempt = self.record['price_attempts'][index]
        attempt['completed_absolute_terms'][name] = part
        attempt['active_stage'] = next_stage
        self.save()

    def evaluate(self, entry: Entry, nu: F):
        context = entry.case.context
        evaluator, key = self.engines[(context, entry.A)], engine.price_key(nu, entry.A, context=context)
        if key in self.record['completed_prices']:
            return evaluator.evaluate(nu)
        if self.record['new_price_attempts'] >= MAX_NEW_PRICES:
            raise RuntimeError('Cumulative THIRTEEN new-price attempt limit reached.')
        attempt = {'key': key, 'parameters': engine.physical_parameters(nu, entry.A, context=context),
                   'status': 'in-progress', 'active_stage': 'first-ODE', 'completed_absolute_terms': {}}
        self.record['price_attempts'].append(attempt)
        self.record['new_price_attempts'] += 1
        self.record['active_price_key'] = key
        self.record['active_price_attempt_index'] = len(self.record['price_attempts'])-1
        self.save()
        try:
            value = evaluator.evaluate(nu)
        except BaseException as error:
            attempt.update({'status': 'interrupted' if isinstance(error, KeyboardInterrupt) else 'failed',
                            'error_kind': type(error).__name__, 'error_message': str(error)})
            self.record['active_price_key'] = self.record['active_price_attempt_index'] = None
            self.save()
            raise
        attempt.update({'status': 'completed', 'active_stage': None})
        self.record['active_price_key'] = self.record['active_price_attempt_index'] = None
        self.save()
        return value

    def stop(self, attempt: dict, reason: str, **details):
        attempt.update({'status': 'failed', 'failure': reason, **details})
        self.record.update({'terminal_failure': True, 'stop_reason': reason, 'active_entry_index': None})
        self.save()

    def run(self):
        if self.record['terminal_failure']:
            return
        for entry in self.entries:
            if any(attempt['name'] == entry.name for attempt in self.record['proved_entries']):
                continue
            context = entry.case.context
            keys = [engine.price_key(nu, entry.A, context=context) for nu in entry.endpoints()]
            attempt = {'name': entry.name, 'entry': entry.record(), 'status': 'in-progress',
                       'endpoint_keys': keys, 'obtained_endpoint_keys': []}
            self.record['entry_attempts'].append(attempt)
            self.record['active_entry_index'] = len(self.record['entry_attempts'])-1
            self.save()
            values = []
            for nu, key in zip(entry.endpoints(), keys):
                try:
                    value = self.evaluate(entry, nu)
                except Exception as error:
                    self.stop(attempt, 'endpoint arithmetic or cumulative budget failed; no automatic retry',
                              failed_price_key=key, error_kind=type(error).__name__, error_message=str(error))
                    return
                attempt['obtained_endpoint_keys'].append(key)
                values.append(value)
                if engine.score(value) >= context.target:
                    self.stop(attempt, 'point/endpoint not strict; no automatic refinement', failed_price_key=key)
                    return
                self.save()
            comparison = max(engine.score(value) for value in values)
            if entry.right is not None:
                theta = engine.RMAX*(entry.right-entry.left)**2/(8*entry.left**2)
                assert 0 <= theta < 1
                factor = 1/(1-theta)
                comparison *= factor
                attempt.update({'theta': str(theta), 'factor': str(factor), 'rmax': str(engine.RMAX)})
            attempt['comparison_upper'] = engine.record_fraction(comparison)
            attempt['strict'] = comparison < context.target
            if comparison >= context.target:
                self.stop(attempt, 'point/chord comparison not strict; no automatic refinement')
                return
            attempt['status'] = 'passed'
            self.record['active_entry_index'] = None
            self.record['proved_entries'].append(attempt)
            self.save()
            print(json.dumps({'i': entry.case.i, 'entry': entry.name,
                              'kind': 'point' if entry.right is None else 'node',
                              'comparison_upper': attempt['comparison_upper']['decimal_upper'], 'strict': True}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--remaining', action='store_true', help='Explicitly run only fixed cases i20/i21/i22.')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--resume-from', type=Path, help='Matching checkpoint; output must be new.')
    args = parser.parse_args()
    if not args.remaining:
        parser.error('Use --remaining explicitly after source review; no prices by default.')
    engine.scalar.base.pin_two_cpus()
    session = RemainingSession(args)
    session.run()
    print(json.dumps({'case_arithmetic_certified': session.record['case_arithmetic_certified'],
                      'three_remaining_cells_arithmetic_certified': session.record['three_remaining_cells_arithmetic_certified'],
                      'new_price_attempts': session.record['new_price_attempts'], 'stop_reason': session.record['stop_reason'],
                      'entire_INITIAL47_certified': False, 'formal_lean_numerical_theorem': False}), flush=True)


if __name__ == '__main__':
    main()
