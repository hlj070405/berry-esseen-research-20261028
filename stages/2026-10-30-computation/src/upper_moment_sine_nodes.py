"""2026-10-30: reusable fixed-upper-moment sine profile; TWO prepared nodes.

No price/integral or JSON write without --nodes.  Fixed U=sigma=7361/4000,
rhoLower=173303/96000,V4,res2048 and one GammaUpper from the true U root.
G_U has the FIXED correction d=1/sigma^2; it is not eta=a/M and is not
refrozen at either endpoint.  W_U is the full two-cap sine primitive.

The evaluation variable nu=s*sigma^2 is an exact Fraction >1 and may be
nonintegral.  Each endpoint is a DETERMINISTIC SPECTRAL PROFILE; no iid sum
with a noninteger sample size is asserted.  Physical roots, raw forcing
sqrt(nu)*H_U, negative-square coefficients 1/nu and 1/(2*nu), and predecessor
coefficient (nu-1)/nu all use the full rational nu and full I arithmetic.
The four absolute terms are summed, then compared as
 sqrt(nu)*Delta/rhoLower=(sigma/rhoLower)*normalized_profile.

Only these two nodes are prepared, without inserting their intervening gap:
 nu in [47,235/4], A4/5; nu in [848/5,212], A2/5.
Both freeze the SAME U,sigma,GammaUpper,A,V,res at their two endpoints.
rmax=3/2, theta=rmax*(b-a)^2/(8*a^2)=3/256 for each node, in nu or s.
The first left price is read literally from the completed n47 pilot after
ALL physical parameters, four terms and ratio match.  It is never rerun.
Only the other THREE endpoint prices may be newly attempted.  A failure
stops the entire two-node plan and preserves its full remaining domain.

Gamma and H are pure extractions of the old RhoBox formulas, with no n field
or RhoBox instance in the evaluator.  The profile ODE never intersects its
state or rows with a Taylor/triangle cap; only its analytic first kernel
cell uses U/(6*sqrt(nu)) and 1/(12*nu).  There is no min-loss seam.

The exponential helper returns an UPPER BOUND ONLY.  For x>=0 it may use
exp(-min(x,32))>=exp(-x), with the existing m8 upper.  Saturated calls and
phases are recorded; no exact exp enclosure outside [0,32] is claimed.
This scalar upper relaxation is not a physical-frequency tail truncation.
It permits the already small nu212 T2 integrand to remain a valid bound.

Atomic checkpoints save completed prices before scoring a node.  Resume
uses a NEW output path and only fully matched completed prices.  Failed,
interrupted and partial attempts remain recorded; partial terms are never
a full price.  Limits are THREE cumulative new attempts, including an
interruption.  No source/result/Lean file is changed, no grid or extra node.
The all-integer-n fixed-G CF theorem has passed Lean; numerical profile and
endpoint/chord bridges are pending and the whole integer band stays FALSE.
Only elapsed-time metadata is floating point.  CPU affinity mask3.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import json
import os
from pathlib import Path
import time

import finite_n_closed_rho_box_pilots as sine_helpers
import n15_reference_circle_boundary_probe as scalar


I, S, ONE, ZERO, PI = scalar.I, scalar.S, scalar.ONE, scalar.ZERO, scalar.PI
rat = scalar.rat
UPPER_MOMENT = SIGMA = F(7361, 4000)
RHO_LOWER = F(173303, 96000)
V, RESOLUTION = F(4), 2048
D, C = 1/SIGMA**2, (UPPER_MOMENT+1)/SIGMA
TARGET = F(27404839, 66655000)
RMAX, MAX_NEW_PRICES = F(3, 2), 3
MODEL = 'fixed-upper-moment-global-complete-sine-real-nu-profile'
FORMAT = 'upper-moment-sine-two-node-probe-v1'
EXP_METHOD = 'm8-upper-exp-minus-min-x-32'
PILOT_FORMAT = 'n47-upper-moment-global-sine-pilot-v1'
PILOT_MODEL = 'upper-moment-fixed-sigma-global-actual-r-complete-sine-quadratic-spectrum'
assert sine_helpers.I is I and sine_helpers.S == S


@dataclass(frozen=True)
class UpperMomentContext:
    """2026-10-30: fixed moment cell; sigma=U, with no numerical candidates."""
    U: F = UPPER_MOMENT
    rhoLower: F = RHO_LOWER
    target: F = TARGET
    sigma: F | None = None

    def __post_init__(self):
        for name in ('U', 'rhoLower', 'target'):
            value = getattr(self, name)
            assert not isinstance(value, float)
            object.__setattr__(self, name, F(value))
        assert self.sigma is None or not isinstance(self.sigma, float)
        object.__setattr__(self, 'sigma', self.U if self.sigma is None else F(self.sigma))
        assert self.sigma == self.U and self.U > 1 and 0 < self.rhoLower <= self.U and self.target > 0

    @property
    def d(self) -> F:
        return 1/self.sigma**2

    @property
    def c(self) -> F:
        return (self.U+1)/self.sigma


DEFAULT_CONTEXT = UpperMomentContext()


@lru_cache(maxsize=16)
def gamma_root_interval(U: F = UPPER_MOMENT) -> I:
    """Pure RhoBox.gamma formula at U; no sample-size dependency."""
    rho = rat(U)
    inner = (rho.sqr()-4+rho*(rho.sqr()+8).sqrt())/2
    assert inner.lo > 0
    return inner.sqrt()


def h_complete(U: F, u: I) -> I:
    """Pure RhoBox.h_complete formula at U; both sine caps retained."""
    rho = rat(U)
    assert u.lo >= 0
    z = sine_helpers.min_interval(u, PI/rho)
    w = sine_helpers.min_interval(u, PI/2)
    sh, _ = sine_helpers.sincos(rho*z/4)
    sw, cw = sine_helpers.sincos(w)
    first = 8*sh.sqr()/rho+2*(u-z).nonneg()
    second = (sw-w*cw).nonneg()+(u.sqr()-w.sqr()).nonneg()/2
    return (first+second).upper()


def fixed_parameters(*, context: UpperMomentContext = DEFAULT_CONTEXT) -> dict:
    gamma = gamma_root_interval(context.U)
    return {'U': str(context.U), 'sigma': str(context.sigma), 'rhoLower': str(context.rhoLower),
            'Gamma_interval_numerators': [str(gamma.lo), str(gamma.hi)],
            'GammaUpper_numerator': str(gamma.hi), 'd': str(context.d), 'c': str(context.c),
            'V': str(V), 'resolution': RESOLUTION, 'scale': str(S), 'target': str(context.target),
            'G_correction': 'fixed 1/sigma^2; not a/M', 'W': 'sigma*H_U(v/sigma)',
            'rmax': str(RMAX), 'exp_method': EXP_METHOD, 'max_new_price_attempts': MAX_NEW_PRICES}


def exact_fraction(value) -> F:
    assert not isinstance(value, float)
    return F(value)


def price_key(nu: F, A: F, *, context: UpperMomentContext = DEFAULT_CONTEXT) -> str:
    gamma_upper = gamma_root_interval(context.U).hi
    return (f'{MODEL}|nu={nu}|U={context.U}|sigma={context.sigma}|GammaUpper={gamma_upper}/{S}'
            f'|rhoLower={context.rhoLower}|A={A}|V={V}|res={RESOLUTION}|exp={EXP_METHOD}')


def physical_parameters(nu: F, A: F, *, context: UpperMomentContext = DEFAULT_CONTEXT) -> dict:
    assert nu > 1 and 0 < A < V and A*A*nu/context.sigma**2 < 64
    root = rat(nu).sqrt()
    beta = rat(context.sigma)/root
    u0, upper = rat(A)*root/rat(context.sigma), rat(V)*root/rat(context.sigma)
    gamma = gamma_root_interval(context.U)
    return {'model': MODEL, 'nu': str(nu), 's': str(nu/context.sigma**2), 'U': str(context.U),
            'sigma': str(context.sigma), 'rhoLower': str(context.rhoLower), 'd': str(context.d),
            's_minus_d': str((nu-1)/context.sigma**2), 'c': str(context.c), 'A': str(A), 'V': str(V),
            'resolution': RESOLUTION, 'scale': str(S),
            'sqrt_nu_interval_numerators': [str(root.lo), str(root.hi)],
            'beta_interval_numerators': [str(beta.lo), str(beta.hi)],
            'physical_U0_interval_numerators': [str(u0.lo), str(u0.hi)],
            'physical_Ufreq_interval_numerators': [str(upper.lo), str(upper.hi)],
            'gamma_root_interval_numerators': [str(gamma.lo), str(gamma.hi)],
            'gamma_upper_numerator': str(gamma.hi), 'old_negative_square_coefficient': str(1/nu),
            'reference_negative_square_coefficient': str(1/(2*nu)),
            'predecessor_exponent_coefficient': str((nu-1)/nu),
            'analytic_head_cubic_coefficient': 'U/(6*sqrt(nu))',
            'analytic_head_quartic_coefficient': str(1/(12*nu)),
            'exact_A_squared_s': str(A*A*nu/context.sigma**2), 'exp_method': EXP_METHOD}


@lru_cache(maxsize=2)
def mesh(A: F) -> tuple[list, list, list]:
    assert 0 < A < V
    first, correction, second = [None], [], []
    for j in range(RESOLUTION):
        za, zb = rat(A*F(j, RESOLUTION)/V), rat(A*F(j+1, RESOLUTION)/V)
        if j:
            first.append(scalar.kernel.rational_kernel_upper(za))
        correction.append(scalar.kernel.rational_correction_upper(I.box(za, zb), first_cell=(j == 0)))
        second.append(scalar.kernel.rational_kernel_upper(rat((A+(V-A)*F(j, RESOLUTION))/V)))
    assert [len(x) for x in (first, correction, second)] == [RESOLUTION]*3
    return first, correction, second


def corrected_exponent_upper(raw_squared: int, raw_linear: int, nu: F) -> int:
    assert raw_squared <= 0 and raw_linear <= 0 and nu > 1
    old, reference = I(raw_squared, raw_squared), I(raw_linear, raw_linear)
    old_corrected = old-rat(1/nu)*old.sqr()
    reference_corrected = reference-rat(1/(2*nu))*reference.sqr()
    return min(0, old_corrected.hi, reference_corrected.hi)


class UpperMomentSineEvaluator:
    def __init__(self, A, completed_prices=None, on_change=None, on_part=None, *,
                 context: UpperMomentContext = DEFAULT_CONTEXT):
        self.A = exact_fraction(A)
        assert 0 < self.A < V
        assert isinstance(context, UpperMomentContext)
        self.context = context
        self.completed_prices = {} if completed_prices is None else completed_prices
        self.on_change, self.on_part = on_change, on_part

    def validate(self, result: dict):
        p = result['parameters']
        nu = F(p['nu'])
        assert p == physical_parameters(nu, self.A, context=self.context)
        parts = result['parts_delta_upper']
        assert len(parts) == 4 and all(x['denominator'] == str(S) and int(x['upper_numerator']) >= 0 for x in parts)
        total = sum(int(x['upper_numerator']) for x in parts)
        assert result['delta_upper']['denominator'] == str(S)
        assert int(result['delta_upper']['upper_numerator']) == total
        expected_ratio = (rat(nu).sqrt()*I(total, total)/rat(self.context.rhoLower)).upper()
        assert result['ratio_upper'] == scalar.base.rational_text(expected_ratio)
        assert result['first_ODE_cells'] == result['T2_cells'] == result['T3_cells'] == RESOLUTION
        assert result['mesh_lengths'] == [RESOLUTION]*3
        assert result['profile_state_intersected_with_cap'] is False
        assert result['profile_integrand_intersected_with_cap'] is False
        assert result['noninteger_iid_sum_claimed'] is False
        assert result['saturation']['returns_upper_bound_only'] is True

    def evaluate(self, nu) -> dict:
        nu = exact_fraction(nu)
        context = self.context
        parameters = physical_parameters(nu, self.A, context=context)
        key = price_key(nu, self.A, context=context)
        if key in self.completed_prices:
            result = self.completed_prices[key]
            self.validate(result)
            return result
        A, root = self.A, rat(nu).sqrt()
        beta = rat(context.sigma)/root
        u0, upper = rat(A)*root/rat(context.sigma), rat(V)*root/rat(context.sigma)
        gamma_upper, coefficient = gamma_root_interval(context.U).upper(), rat(context.c)
        cubics = ((I.rat(1, 2), (coefficient/10)*beta),
                  (scalar.OLD_THETA_A, scalar.OLD_THETA_B*coefficient*beta),
                  (I.rat(1, 100), (coefficient/625)*beta),
                  (scalar.NEW_THETA_A, scalar.NEW_THETA_B*coefficient*beta))
        saturation = {'used': False, 'clipped_interval_calls': 0, 'calls_by_phase': {},
                      'threshold': '32', 'max_argument_upper_numerator': '0',
                      'returns_upper_bound_only': True, 'exact_exp_enclosure_claimed': False,
                      'physical_frequency_tail_truncated': False}

        def exp_upper(x: I, phase: str) -> I:
            assert x.lo >= 0
            saturation['max_argument_upper_numerator'] = str(max(int(saturation['max_argument_upper_numerator']), x.hi))
            if x.hi > 32*S:
                saturation['used'] = True
                saturation['clipped_interval_calls'] += 1
                counts = saturation['calls_by_phase']
                counts[phase] = counts.get(phase, 0)+1
            # scalar helper returns exp(-min(x,32)) UPPER, hence also >=exp(-x).
            # It is deliberately not used as a Contains-exact-exp interval.
            return scalar.exp_minus_upper(x)

        def rate_upper(t: I) -> int:
            assert t.lo >= 0
            left, right = I(t.lo, t.lo), I(t.hi, t.hi)
            old_bounds = []
            for quadratic, cubic in cubics:
                ea = -quadratic*left.sqr()+cubic*(left**3)
                eb = -quadratic*right.sqr()+cubic*(right**3)
                old_bounds.append(max(ea.hi, eb.hi))
            E4 = min(0, *old_bounds)
            u = t/root
            radius = 5*rat(context.U)*(u**3)/48
            center_norm = ((ONE-u.sqr()/2).sqr()+(gamma_upper*(u**3)/16).sqr()).sqrt()
            Eref = min(0, (rat(nu)*(radius+center_norm-1)).hi)
            return corrected_exponent_upper(E4, Eref, nu)

        def emit(name: str, term: I, next_stage: str):
            if self.on_part:
                self.on_part(key, name, scalar.base.rational_text(term), next_stage)

        first_mesh, corrections, second_mesh = mesh(A)
        dt, state, sum1 = u0/RESOLUTION, ZERO, ZERO
        for j in range(RESOLUTION):
            a, b = u0*I.rat(j, RESOLUTION), u0*I.rat(j+1, RESOLUTION)
            E = rate_upper(I.box(a, b))
            pred_exponent = rat((nu-1)/nu)*I(E, E)
            assert pred_exponent.hi <= 0
            q_pred = exp_upper(-pred_exponent, 'first-ODE')
            force = (root*q_pred*h_complete(context.U, b/root)).upper()
            end = (exp_upper((b.sqr()-a.sqr()).nonneg()/2, 'first-ODE')*state+force*dt).upper()
            in_cell = (state+force*dt).upper()
            if j == 0:
                c, d = rat(context.U)/(6*root), rat(1/(12*nu))
                first = (c*(b**4)/8+d*(b**5)/10+upper*c*(b**3)/(6*PI)+upper*d*(b**4)/(8*PI))
                sum1 = sum1+first
            else:
                sum1 = sum1+dt*first_mesh[j]*in_cell
            state = end  # Global profile only; never intersect with an actual-error cap.
        T1 = (2*sum1/upper).upper()
        emit('T1', T1, 'T2')
        sum2 = ZERO
        for j in range(RESOLUTION):
            a = u0+(upper-u0)*I.rat(j, RESOLUTION)
            b = u0+(upper-u0)*I.rat(j+1, RESOLUTION)
            E = rate_upper(I.box(a, b))
            q_power = exp_upper(I(-E, -E), 'T2')
            sum2 = sum2+(upper-u0)/RESOLUTION*second_mesh[j]*q_power
        T2 = (2*sum2/upper).upper()
        emit('T2', T2, 'T3')
        sum3 = ZERO
        for j in range(RESOLUTION):
            t = u0*I.rat(j, RESOLUTION)
            sum3 = sum3+dt*corrections[j]*exp_upper(t.sqr()/2, 'T3')
        T3 = (2*sum3/upper).upper()
        emit('T3', T3, 'T4')
        mills4 = exp_upper(rat(A*A*nu/(2*context.sigma**2)), 'T4')/(PI*rat(A*A*nu/context.sigma**2))
        T4, fourth_choice, tail_cells = mills4, 'Mills', 0
        if A*A*nu/context.sigma**2 < 36:
            tail_end, finite_tail = I.rat(6), ZERO
            assert u0.hi < tail_end.lo
            for j in range(RESOLUTION):
                t = u0+(tail_end-u0)*I.rat(j, RESOLUTION)
                finite_tail = finite_tail+(tail_end-u0)/RESOLUTION*exp_upper(t.sqr()/2, 'T4')/t
            riemann4 = finite_tail/PI+exp_upper(tail_end.sqr()/2, 'T4')/(PI*tail_end.sqr())
            T4 = scalar.base.min_upper(mills4, riemann4)
            fourth_choice = 'Mills' if mills4.hi <= riemann4.hi else 'Riemann_to_6_plus_tail'
            tail_cells = RESOLUTION
        emit('T4', T4, 'completed-price')
        parts = [scalar.base.rational_text(x) for x in (T1, T2, T3, T4)]
        total = sum(int(x['upper_numerator']) for x in parts)
        delta = I(total, total)
        ratio = (root*delta/rat(context.rhoLower)).upper()
        result = {'parameters': parameters, 'parts_delta_upper': parts,
                  'delta_upper': scalar.base.rational_text(delta), 'ratio_upper': scalar.base.rational_text(ratio),
                  'comparison_quantity': '(sigma/rhoLower)*normalized_profile = sqrt(nu)*absolute_Delta/rhoLower',
                  'first_ODE_cells': RESOLUTION, 'T2_cells': RESOLUTION, 'T3_cells': RESOLUTION,
                  'T4_finite_tail_cells': tail_cells, 'mesh_lengths': [len(x) for x in mesh(A)],
                  'fourth_bound_selected': fourth_choice, 'profile_ODE_terminal_upper': scalar.base.rational_text(state),
                  'profile_state_intersected_with_cap': False, 'profile_integrand_intersected_with_cap': False,
                  'noninteger_iid_sum_claimed': False, 'saturation': saturation}
        self.validate(result)
        self.completed_prices[key] = result
        if self.on_change:
            self.on_change()  # Completed full price is durable BEFORE node scoring.
        return result


@dataclass(frozen=True)
class SpectralNode:
    name: str
    left: F
    right: F
    A: F

    def record(self, *, context: UpperMomentContext = DEFAULT_CONTEXT) -> dict:
        assert 1 < self.left < self.right
        assert 0 < self.A < V and self.A*self.A*self.right/context.sigma**2 < 64
        theta = RMAX*(self.right-self.left)**2/(8*self.left**2)
        assert 0 <= theta < 1
        return {'name': self.name, 'nu_left': str(self.left), 'nu_right': str(self.right),
                's_left': str(self.left/context.sigma**2), 's_right': str(self.right/context.sigma**2),
                'A': str(self.A), 'rmax': str(RMAX), 'theta': str(theta), 'factor': str(1/(1-theta)),
                'fixed_spectrum_parameters': fixed_parameters(context=context), 'noninteger_iid_sum_claimed': False}


PLANS = (SpectralNode('nu47-to-235over4-A4over5', F(47), F(235, 4), F(4, 5)),
         SpectralNode('nu848over5-to-212-A2over5', F(848, 5), F(212), F(2, 5)))


def score(result: dict) -> F:
    p = result['ratio_upper']
    return F(int(p['upper_numerator']), int(p['denominator']))


def record_fraction(x: F) -> dict:
    return {'upper_numerator': str(x.numerator), 'denominator': str(x.denominator),
            'decimal_upper': rat(x).decimal_upper()}


class NodeSession:
    def __init__(self, args):
        self.args, self.started = args, time.monotonic()
        if args.output.exists():
            raise FileExistsError('Choose a NEW output path; previous results are read-only.')
        assert args.output.parent.exists() and args.seed_json.is_file()
        assert args.output.resolve() != args.seed_json.resolve()
        self.allowed = {price_key(nu, node.A): (node, nu) for node in PLANS for nu in (node.left, node.right)}
        if args.resume_from:
            assert args.output.resolve() != args.resume_from.resolve()
            self.record = json.loads(args.resume_from.read_text(encoding='utf-8'))
            assert self.record['format'] == FORMAT and self.record['model'] == MODEL
            assert self.record['fixed_parameters'] == fixed_parameters()
            assert self.record['plans'] == [node.record() for node in PLANS]
        else:
            self.record = {'format': FORMAT, 'date': '2026-10-30', 'model': MODEL,
                           'fixed_parameters': fixed_parameters(), 'plans': [node.record() for node in PLANS],
                           'completed_prices': {}, 'price_attempts': [], 'node_attempts': [], 'proved_nodes': [],
                           'new_price_attempts': 0, 'active_price_key': None, 'active_price_attempt_index': None,
                           'active_node_index': None, 'terminal_failure': False, 'stop_reason': None,
                           'fixed_G_all_integer_n_CF_Lean_proved': True,
                           'CF_Lean_source': 'BerryEsseen.UpperMomentDamping',
                           'numerical_profile_Lean_proved': False, 'new_endpoint_bridge_Lean_proved': False,
                           'whole_integer_band_certified': False, 'whole_n47_through_212_certified': False,
                           'formal_lean_numerical_theorem': False, 'complete_classical_formula_claimed': False,
                           'unplanned_nu_gap': [['235/4', '848/5']], 'min_loss_switch_used': False,
                           'noninteger_iid_sum_claimed': False, 'affinity_mask': 3}
        self.engines = {node.A: UpperMomentSineEvaluator(node.A, self.record['completed_prices']) for node in PLANS}
        self.load_pilot_seed()
        self.validate_history()
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

    def load_pilot_seed(self):
        old = json.loads(self.args.seed_json.read_text(encoding='utf-8'))
        assert old['format'] == PILOT_FORMAT and old['model'] == PILOT_MODEL and old['status'] == 'completed'
        # All legacy physical fields are checked, including the literal sqrt,
        # gamma, beta and cutoff interval numerators.  No pilot code is imported.
        node, nu = PLANS[0], F(47)
        p = physical_parameters(nu, node.A)
        expected = {'model': PILOT_MODEL, 'actual_n': 47,
                    'actual_rho_closed_box': [str(RHO_LOWER), str(UPPER_MOMENT)],
                    'upper_moment_U': str(UPPER_MOMENT), 'virtual_sigma': str(SIGMA),
                    's': p['s'], 'd': p['d'], 's_minus_d': p['s_minus_d'], 'c_upper_moment': str(C),
                    'A': '4/5', 'V': str(V), 'resolution': RESOLUTION, 'target': str(TARGET), 'scale': str(S),
                    'beta_interval_numerators': p['beta_interval_numerators'],
                    'sqrt_n_interval_numerators': p['sqrt_nu_interval_numerators'],
                    'physical_U0_interval_numerators': p['physical_U0_interval_numerators'],
                    'physical_Ufreq_interval_numerators': p['physical_Ufreq_interval_numerators'],
                    'gamma_root_interval_numerators': p['gamma_root_interval_numerators'],
                    'gamma_upper_numerator': p['gamma_upper_numerator'],
                    'old_negative_square_coefficient': '1/47', 'reference_negative_square_coefficient': '1/94',
                    'predecessor_exponent_coefficient': '46/47',
                    'analytic_head_cubic_coefficient': 'U/(6*sqrt(actual_n))',
                    'analytic_head_quartic_coefficient': '1/564', 'exact_A_squared_s': p['exact_A_squared_s']}
        assert old['parameters'] == expected
        evaluation = old['evaluation']
        assert all(evaluation[k] == RESOLUTION for k in ('actual_first_ODE_cells', 'actual_T2_cells',
                                                        'actual_T3_cells', 'actual_T4_finite_tail_cells'))
        assert evaluation['actual_mesh_lengths'] == [RESOLUTION]*3
        assert evaluation['actual_error_state_intersected_with_cap'] is False
        assert evaluation['actual_error_integrand_intersected_with_cap'] is False
        assert evaluation['exp_saturation_used'] is False
        parts = deepcopy(evaluation['parts_delta_upper'])
        assert all(old['completed_absolute_terms'][name] == part for name, part in zip(('T1', 'T2', 'T3', 'T4'), parts))
        result = {'parameters': p, 'parts_delta_upper': parts, 'delta_upper': deepcopy(evaluation['delta_upper']),
                  'ratio_upper': deepcopy(evaluation['sqrt_n_delta_over_rho_lower_upper']),
                  'comparison_quantity': '(sigma/rhoLower)*normalized_profile = sqrt(nu)*absolute_Delta/rhoLower',
                  'first_ODE_cells': RESOLUTION, 'T2_cells': RESOLUTION, 'T3_cells': RESOLUTION,
                  'T4_finite_tail_cells': RESOLUTION, 'mesh_lengths': [RESOLUTION]*3,
                  'fourth_bound_selected': evaluation['fourth_bound_selected'],
                  'profile_ODE_terminal_upper': deepcopy(evaluation['global_actual_error_ODE_terminal_upper']),
                  'profile_state_intersected_with_cap': False, 'profile_integrand_intersected_with_cap': False,
                  'noninteger_iid_sum_claimed': False,
                  'saturation': {'used': False, 'clipped_interval_calls': 0, 'calls_by_phase': {},
                                 'threshold': '32', 'max_argument_upper_numerator': None,
                                 'returns_upper_bound_only': True, 'exact_exp_enclosure_claimed': False,
                                 'physical_frequency_tail_truncated': False,
                                 'source': 'pilot strict-range assertions; no saturation'},
                  'origin': self.args.seed_json.name}
        self.engines[node.A].validate(result)
        assert score(result) < TARGET
        key = price_key(nu, node.A)
        if key in self.record['completed_prices']:
            cached = self.record['completed_prices'][key]
            assert cached['parts_delta_upper'] == result['parts_delta_upper'] and cached['ratio_upper'] == result['ratio_upper']
        else:
            self.record['completed_prices'][key] = result
        self.record['read_only_pilot_seed'] = self.args.seed_json.name
        self.record['literal_seed_price_key'] = key

    def validate_history(self):
        for key, result in self.record['completed_prices'].items():
            node, nu = self.allowed[key]
            self.engines[node.A].validate(result)
            assert result['parameters'] == physical_parameters(nu, node.A)
        assert len(self.record['price_attempts']) == self.record['new_price_attempts'] <= MAX_NEW_PRICES
        for attempt in self.record['price_attempts']:
            node, nu = self.allowed[attempt['key']]
            assert attempt['parameters'] == physical_parameters(nu, node.A)
            assert attempt['status'] in ('in-progress', 'interrupted', 'failed', 'completed')
        seen = set()
        for attempt in self.record['proved_nodes']:
            node = next(n for n in PLANS if n.name == attempt['name'])
            assert node.name not in seen and attempt['node'] == node.record() and attempt['status'] == 'passed'
            seen.add(node.name)
            keys = [price_key(nu, node.A) for nu in (node.left, node.right)]
            assert attempt['endpoint_keys'] == keys
            theta = RMAX*(node.right-node.left)**2/(8*node.left**2)
            joint = max(score(self.record['completed_prices'][key]) for key in keys)/(1-theta)
            assert F(attempt['theta']) == theta and F(attempt['factor']) == 1/(1-theta)
            p = attempt['joint_upper']
            assert F(int(p['upper_numerator']), int(p['denominator'])) == joint < TARGET

    def atomic_save(self):
        passed = {attempt['name'] for attempt in self.record['proved_nodes']}
        remaining = [node for node in PLANS if node.name not in passed]
        self.record['remaining_prepared_nodes'] = [node.record() for node in remaining]
        self.record['unresolved_prepared_nu_domain'] = [[str(node.left), str(node.right)] for node in remaining]
        self.record['two_prepared_nodes_arithmetic_certified_given_pending_bridges'] = not remaining
        self.record['current_invocation_elapsed_seconds_metadata'] = time.monotonic()-self.started
        temp = self.args.output.with_name(self.args.output.name+'.tmp')
        with temp.open('w', encoding='utf-8', newline='\n') as handle:
            json.dump(self.record, handle, indent=2)
            handle.write('\n')
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp, self.args.output)

    def save_part(self, key: str, name: str, part: dict, next_stage: str):
        index = self.record['active_price_attempt_index']
        assert index is not None and self.record['price_attempts'][index]['key'] == key
        attempt = self.record['price_attempts'][index]
        attempt['completed_absolute_terms'][name] = part
        attempt['active_stage'] = next_stage
        self.atomic_save()

    def evaluate(self, node: SpectralNode, nu: F) -> dict:
        evaluator, key = self.engines[node.A], price_key(nu, node.A)
        if key in self.record['completed_prices']:
            return evaluator.evaluate(nu)
        if self.record['new_price_attempts'] >= MAX_NEW_PRICES:
            raise RuntimeError('Cumulative THREE new-price attempt limit reached.')
        attempt = {'key': key, 'parameters': physical_parameters(nu, node.A), 'status': 'in-progress',
                   'active_stage': 'first-ODE', 'completed_absolute_terms': {}, 'partial_terms_are_a_full_price': False}
        self.record['price_attempts'].append(attempt)
        self.record['new_price_attempts'] += 1
        self.record['active_price_attempt_index'] = len(self.record['price_attempts'])-1
        self.record['active_price_key'] = key
        self.atomic_save()
        try:
            result = evaluator.evaluate(nu)
        except BaseException as error:
            attempt.update({'status': 'interrupted' if isinstance(error, KeyboardInterrupt) else 'failed',
                            'error_kind': type(error).__name__, 'error_message': str(error)})
            self.record['active_price_attempt_index'] = self.record['active_price_key'] = None
            self.atomic_save()
            raise
        attempt.update({'status': 'completed', 'active_stage': None})
        self.record['active_price_attempt_index'] = self.record['active_price_key'] = None
        self.atomic_save()
        return result

    def stop(self, attempt: dict, reason: str, **details):
        attempt.update({'status': 'failed', 'failure': reason, **details})
        self.record.update({'terminal_failure': True, 'stop_reason': reason, 'active_node_index': None})
        self.atomic_save()

    def run(self):
        if self.record['terminal_failure']:
            return
        for node in PLANS:
            if any(attempt['name'] == node.name for attempt in self.record['proved_nodes']):
                continue
            keys = [price_key(nu, node.A) for nu in (node.left, node.right)]
            attempt = {'name': node.name, 'node': node.record(), 'status': 'in-progress',
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
                if score(value) >= TARGET:
                    self.stop(attempt, 'endpoint not strict; no automatic subdivision', failed_price_key=key)
                    return
                self.atomic_save()
            theta = RMAX*(node.right-node.left)**2/(8*node.left**2)
            assert 0 <= theta < 1
            factor, joint = 1/(1-theta), max(score(value) for value in values)/(1-theta)
            attempt.update({'rmax': str(RMAX), 'theta': str(theta), 'factor': str(factor),
                            'joint_upper': record_fraction(joint), 'strict_joint': joint < TARGET})
            if joint >= TARGET:
                self.stop(attempt, 'Fraction chord joint not strict; no automatic subdivision')
                return
            attempt['status'] = 'passed'
            self.record['active_node_index'] = None
            self.record['proved_nodes'].append(attempt)
            self.atomic_save()
            print(json.dumps({'node': node.name, 'nu': [str(node.left), str(node.right)], 'A': str(node.A),
                              'joint_upper': attempt['joint_upper']['decimal_upper'], 'strict_joint': True}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nodes', action='store_true', help='Explicitly run ONLY the two prepared fixed-G nodes.')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--resume-from', type=Path, help='Matching checkpoint; --output must be new.')
    parser.add_argument('--seed-json', type=Path, default=Path(__file__).with_name('n47_upper_moment_global_sine_pilot.json'))
    args = parser.parse_args()
    if not args.nodes:
        parser.error('Use --nodes explicitly after source review; no numerical work by default.')
    scalar.base.pin_two_cpus()
    session = NodeSession(args)
    session.run()
    print(json.dumps({'two_prepared_nodes_arithmetic_certified_given_pending_bridges':
                      session.record['two_prepared_nodes_arithmetic_certified_given_pending_bridges'],
                      'new_price_attempts': session.record['new_price_attempts'], 'stop_reason': session.record['stop_reason'],
                      'unresolved_prepared_nu_domain': session.record['unresolved_prepared_nu_domain'],
                      'whole_integer_band_certified': False, 'formal_lean_numerical_theorem': False}), flush=True)


if __name__ == '__main__':
    main()
