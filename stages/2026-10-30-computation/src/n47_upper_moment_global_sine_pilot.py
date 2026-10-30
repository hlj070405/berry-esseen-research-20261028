"""2026-10-30: ONE upper-moment, global actual-error sine pilot; PREPARED ONLY.

No integral/price or JSON write without explicit --pilot.  Fix actual n=47,
actual rho in [173303/96000,U], U=sigma=7361/4000, A4/5,V4,res2048.
The target for sqrt(47)*Delta/rho_lower is 27404839/66655000.  Sigma is a
virtual upper-moment normalization scale, not a distribution or a claim
that actual rho>=sigma.  No other n,rho,A,res, parameter search or cover.

Let beta=sigma/sqrt(n), v=beta*t, s=n/sigma^2, d=1/sigma^2 and
W_U(v)=sigma*H_U(v/sigma), where H_U is the FULL two-cap sine primitive.
The actual residual r has forcing sqrt(n)*q^(n-1)*H_U(t/sqrt(n)).
For r/beta this forcing is s*W_U(v)*exp((s-d)*G_U(v)); after the frequency
change the Volterra core is exactly
 s^(3/2)*exp[-s*(v^2-w^2)/2+(s-d)*G_U(w)]*W_U(w).
Thus there is one p=3/2 positive-Laplace spectral object and no min-loss seam.
This pilot evaluates its physical actual-r ODE, without a Taylor/triangle
minimum in either a row or the propagated state.  The analytic first kernel
cell alone uses r(t)<=U*t^3/(6*sqrt(n))+t^4/(12*n), as in the old sine price.

With c=(U+1)/sigma the FOUR RAW SQUARED-CF branches give g4.  The raw linear
reference uses the TRUE moment-region root
 Gamma(U)=sqrt((U^2-4+U*sqrt(U^2+8))/2), enclosed upward, not a chosen gamma.
Its spectral rate is
 Hbar_U(v)=5*(U/sigma)*|v|^3/48
  +sqrt((sigma^2-v^2/2)^2+(Gamma(U)/sigma)^2*v^6/256)-sigma^2.
Write h=min(0,Hbar_U) and
 G_U=min(g4-g4^2/sigma^2,h-h^2/(2*sigma^2)).
For this physical n47 calculation, E4 is the whole-cell cubic endpoint max
and Eref is the WHOLE-INTERVAL expression
 n*(5*U*|u|^3/48+sqrt((1-u^2/2)^2+(GammaUpper*u^3/16)^2)-1),
u=t/sqrt(n).  Clip each raw branch upper to <=0 BEFORE the correction.
The common n-th-power exponent is min(E4-E4^2/47,Eref-Eref^2/94,0).
Coefficients, squares and negative subtractions retain FULL I intervals;
only the final corrected upper endpoints are selected.  The predecessor
power is exp((46/47)*E), also with a full signed interval multiplication.

The global ODE force on [a,b] is sqrt(47)*qPred*RhoBox.h_complete(b/sqrt(47)).
T1 and T2 are ABSOLUTE Delta terms with prefactor 2/physical_upper_frequency.
T3/T4 are recomputed at these same physical A,V,s: four-pole correction,
m8 exponentials, and Mills or Riemann-to-6 Gaussian tail.  The four absolute
terms are summed once, then multiplied by sqrt(47)/rho_lower.  No old CF,
ODE, Gaussian term, or price cache is reused.  No P6, actual-error cap,
phase cap, loss switch, physical tail cap, float quadrature, or fake CF.

Existing integer I, m8 exp, four-pole kernel, true moment root and complete
sine helpers are reused without mutation.  Every exp argument is checked
in [0,32] BEFORE the old helper, so its saturation is never used.  New
upper-moment normalized/pred CF, actual-error/spectral and Laplace bridges
are NOT yet Lean theorems and remain FALSE in JSON even if arithmetic passes.
This is a route-selection pilot, not a formal numerical or classical theorem.
Only elapsed-time metadata is floating point.  CPU affinity mask3.
Old files/results/Lean are read-only.  A new output path is mandatory if
the default already exists.  Completed absolute terms and any failure are
atomically retained; partial terms alone are never a complete bound.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
import json
import os
from pathlib import Path
import time

import finite_n_closed_rho_box_pilots as finite_sine
import n15_reference_circle_boundary_probe as scalar


I, S, ONE, ZERO, PI = scalar.I, scalar.S, scalar.ONE, scalar.ZERO, scalar.PI
rat = scalar.rat
N, RESOLUTION = 47, 2048
SIGMA = F(7361, 4000)
UPPER_MOMENT = SIGMA
RHO_LOWER = F(173303, 96000)
A, V = F(4, 5), F(4)
S_POINT, D = F(N)/SIGMA**2, 1/SIGMA**2
C = (UPPER_MOMENT+1)/SIGMA
TARGET = F(27404839, 66655000)
MODEL = 'upper-moment-fixed-sigma-global-actual-r-complete-sine-quadratic-spectrum'
FORMAT = 'n47-upper-moment-global-sine-pilot-v1'
assert finite_sine.I is I and finite_sine.S == S
assert RHO_LOWER < UPPER_MOMENT == SIGMA and C*SIGMA == UPPER_MOMENT+1
assert S_POINT-D == F(N-1)/SIGMA**2 and 0 < A < V
assert A*A*S_POINT < 36 < 64


def exp_minus_upper(x: I) -> I:
    """Reuse m8 only on its true range; never invoke its >32 saturation."""
    assert 0 <= x.lo <= x.hi <= 32*S
    return scalar.exp_minus_upper(x)


@lru_cache(maxsize=1)
def mesh() -> tuple[list, list, list]:
    first, correction, second = [None], [], []
    for j in range(RESOLUTION):
        za, zb = rat(A*F(j, RESOLUTION)/V), rat(A*F(j+1, RESOLUTION)/V)
        if j:
            first.append(scalar.kernel.rational_kernel_upper(za))
        correction.append(scalar.kernel.rational_correction_upper(I.box(za, zb), first_cell=(j == 0)))
        second.append(scalar.kernel.rational_kernel_upper(rat((A+(V-A)*F(j, RESOLUTION))/V)))
    assert [len(x) for x in (first, correction, second)] == [RESOLUTION]*3
    return first, correction, second


def corrected_power_exponent_upper(raw_squared: int, raw_linear: int) -> int:
    assert raw_squared <= 0 and raw_linear <= 0
    old, reference = I(raw_squared, raw_squared), I(raw_linear, raw_linear)
    # The negative subtraction is the critical outward-arithmetic direction.
    # Do not replace either coefficient or squared enclosure by an upper point.
    old_corrected = old-rat(F(1, N))*old.sqr()
    reference_corrected = reference-rat(F(1, 2*N))*reference.sqr()
    return min(0, old_corrected.hi, reference_corrected.hi)


class UpperMomentN47Pilot:
    def __init__(self):
        self.box = finite_sine.RhoBox(N, RHO_LOWER, UPPER_MOMENT, TARGET, str(UPPER_MOMENT))
        self.root_n = self.box.root
        self.gamma_interval = self.box.gamma
        self.gamma_upper = self.gamma_interval.upper()
        self.beta = rat(SIGMA)/self.root_n
        self.u0 = rat(A)*self.root_n/rat(SIGMA)
        self.upper_frequency = rat(V)*self.root_n/rat(SIGMA)
        assert 0 < self.u0.lo < self.u0.hi < self.upper_frequency.lo
        assert self.u0.hi < 6*S
        coefficient = rat(C)
        self.cubics = ((I.rat(1, 2), (coefficient/10)*self.beta),
                       (scalar.OLD_THETA_A, scalar.OLD_THETA_B*coefficient*self.beta),
                       (I.rat(1, 100), (coefficient/625)*self.beta),
                       (scalar.NEW_THETA_A, scalar.NEW_THETA_B*coefficient*self.beta))
        assert all(a.lo > 0 and b.lo > 0 for a, b in self.cubics)

    def parameters(self) -> dict:
        return {'model': MODEL, 'actual_n': N, 'actual_rho_closed_box': [str(RHO_LOWER), str(UPPER_MOMENT)],
                'upper_moment_U': str(UPPER_MOMENT), 'virtual_sigma': str(SIGMA),
                's': str(S_POINT), 'd': str(D), 's_minus_d': str(S_POINT-D),
                'c_upper_moment': str(C), 'A': str(A), 'V': str(V), 'resolution': RESOLUTION,
                'target': str(TARGET), 'scale': str(S),
                'beta_interval_numerators': [str(self.beta.lo), str(self.beta.hi)],
                'sqrt_n_interval_numerators': [str(self.root_n.lo), str(self.root_n.hi)],
                'physical_U0_interval_numerators': [str(self.u0.lo), str(self.u0.hi)],
                'physical_Ufreq_interval_numerators': [str(self.upper_frequency.lo), str(self.upper_frequency.hi)],
                'gamma_root_interval_numerators': [str(self.gamma_interval.lo), str(self.gamma_interval.hi)],
                'gamma_upper_numerator': str(self.gamma_upper.hi),
                'old_negative_square_coefficient': str(F(1, N)),
                'reference_negative_square_coefficient': str(F(1, 2*N)),
                'predecessor_exponent_coefficient': str(F(N-1, N)),
                'analytic_head_cubic_coefficient': 'U/(6*sqrt(actual_n))',
                'analytic_head_quartic_coefficient': str(F(1, 12*N)),
                'exact_A_squared_s': str(A*A*S_POINT)}

    def power_exponent_upper(self, t: I) -> int:
        assert t.lo >= 0
        left, right = I(t.lo, t.lo), I(t.hi, t.hi)
        cubic_uppers = []
        # Every true cubic has negative quadratic and positive cubic terms:
        # on a nonnegative interval its maximum is at one of the endpoints.
        # These are RAW SQUARED-CF polynomials, not old exponential outputs.
        for quadratic, cubic in self.cubics:
            ea = -quadratic*left.sqr()+cubic*(left**3)
            eb = -quadratic*right.sqr()+cubic*(right**3)
            cubic_uppers.append(max(ea.hi, eb.hi))
        E4 = min(0, *cubic_uppers)
        u = t/self.root_n
        assert u.lo >= 0
        radius = 5*rat(UPPER_MOMENT)*(u**3)/48
        # Keep the real center SIGNED before squaring, including when it
        # crosses zero on a whole T2 cell.  GammaUpper bounds actual |gamma|.
        center_norm = ((ONE-u.sqr()/2).sqr()+(self.gamma_upper*(u**3)/16).sqr()).sqrt()
        reference_full = N*(radius+center_norm-1)
        Eref = min(0, reference_full.hi)
        return corrected_power_exponent_upper(E4, Eref)

    def q_power_upper(self, t: I) -> I:
        E = self.power_exponent_upper(t)
        return exp_minus_upper(I(-E, -E))

    def q_predecessor_upper(self, t: I) -> I:
        E = self.power_exponent_upper(t)
        # Full multiplication matters: E<=0 reverses coefficient endpoint use.
        predecessor_exponent = rat(F(N-1, N))*I(E, E)
        assert predecessor_exponent.hi <= 0
        return exp_minus_upper(-predecessor_exponent)

    def evaluate(self, on_part=None) -> dict:
        first_mesh, corrections, second_mesh = mesh()
        dt, rstart, sum1 = self.u0/RESOLUTION, ZERO, ZERO
        for j in range(RESOLUTION):
            a = self.u0*I.rat(j, RESOLUTION)
            b = self.u0*I.rat(j+1, RESOLUTION)
            q_pred = self.q_predecessor_upper(I.box(a, b))
            complete_sine = self.box.h_complete(b/self.root_n)
            force = (self.root_n*q_pred*complete_sine).upper()
            rend = (exp_minus_upper((b.sqr()-a.sqr()).nonneg()/2)*rstart+force*dt).upper()
            in_cell = (rstart+force*dt).upper()
            if j == 0:
                c = rat(UPPER_MOMENT)/(6*self.root_n)
                d = rat(F(1, 12*N))
                first = (c*(b**4)/8+d*(b**5)/10+
                         self.upper_frequency*c*(b**3)/(6*PI)+
                         self.upper_frequency*d*(b**4)/(8*PI))
                sum1 = sum1+first
            else:
                sum1 = sum1+dt*first_mesh[j]*in_cell
            # GLOBAL actual-r ODE: no Taylor, triangle, or actual-error minimum.
            rstart = rend
        T1 = (2*sum1/self.upper_frequency).upper()
        if on_part:
            on_part('T1', T1, 'T2')

        sum2 = ZERO
        for j in range(RESOLUTION):
            a = self.u0+(self.upper_frequency-self.u0)*I.rat(j, RESOLUTION)
            b = self.u0+(self.upper_frequency-self.u0)*I.rat(j+1, RESOLUTION)
            q_power = self.q_power_upper(I.box(a, b))
            sum2 = sum2+(self.upper_frequency-self.u0)/RESOLUTION*second_mesh[j]*q_power
        T2 = (2*sum2/self.upper_frequency).upper()
        if on_part:
            on_part('T2', T2, 'T3')

        sum3 = ZERO
        for j in range(RESOLUTION):
            t = self.u0*I.rat(j, RESOLUTION)
            sum3 = sum3+dt*corrections[j]*exp_minus_upper(t.sqr()/2)
        T3 = (2*sum3/self.upper_frequency).upper()
        if on_part:
            on_part('T3', T3, 'T4')

        tail_end, finite_tail = I.rat(6), ZERO
        for j in range(RESOLUTION):
            t = self.u0+(tail_end-self.u0)*I.rat(j, RESOLUTION)
            finite_tail = finite_tail+(tail_end-self.u0)/RESOLUTION*exp_minus_upper(t.sqr()/2)/t
        riemann4 = finite_tail/PI+exp_minus_upper(tail_end.sqr()/2)/(PI*tail_end.sqr())
        mills4 = exp_minus_upper(rat(A*A*S_POINT/2))/(PI*rat(A*A*S_POINT))
        T4 = scalar.base.min_upper(mills4, riemann4)
        fourth_choice = 'Mills' if mills4.hi <= riemann4.hi else 'Riemann_to_6_plus_tail'
        if on_part:
            on_part('T4', T4, 'final-score')

        parts = [scalar.base.rational_text(term) for term in (T1, T2, T3, T4)]
        assert all(term['denominator'] == str(S) and int(term['upper_numerator']) >= 0 for term in parts)
        total_numerator = sum(int(term['upper_numerator']) for term in parts)
        delta = I(total_numerator, total_numerator)
        ratio = (self.root_n*delta/rat(RHO_LOWER)).upper()
        strict = F(ratio.hi, S) < TARGET
        return {'parts_delta_upper': parts, 'delta_upper': scalar.base.rational_text(delta),
                'sqrt_n_delta_over_rho_lower_upper': scalar.base.rational_text(ratio),
                'target': str(TARGET), 'arithmetic_strict_success_given_pending_bridges': strict,
                'strict_margin_lower_numerator': str((rat(TARGET)-ratio).lo), 'denominator': str(S),
                'actual_first_ODE_cells': RESOLUTION, 'actual_T2_cells': RESOLUTION,
                'actual_T3_cells': RESOLUTION, 'actual_T4_finite_tail_cells': RESOLUTION,
                'actual_mesh_lengths': [len(x) for x in mesh()], 'fourth_bound_selected': fourth_choice,
                'global_actual_error_ODE_terminal_upper': scalar.base.rational_text(rstart),
                'actual_error_state_intersected_with_cap': False,
                'actual_error_integrand_intersected_with_cap': False,
                'only_first_cell_uses_analytic_head': True, 'all_four_terms_recomputed': True,
                'old_price_or_gaussian_cache_reused': False, 'exp_saturation_used': False}


def atomic_save(path: Path, record: dict):
    temp = path.with_name(path.name+'.tmp')
    with temp.open('w', encoding='utf-8', newline='\n') as handle:
        json.dump(record, handle, indent=2)
        handle.write('\n')
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temp, path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pilot', action='store_true', help='Explicitly run ONLY the prepared n47 pilot.')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    if not args.pilot:
        parser.error('Use --pilot explicitly after source review; no numerical work by default.')
    if args.output.exists():
        raise FileExistsError('Choose a NEW output path; existing sources/results are read-only.')
    assert args.output.parent.exists()
    scalar.base.pin_two_cpus()
    started = time.monotonic()
    pilot = UpperMomentN47Pilot()
    record = {'format': FORMAT, 'date': '2026-10-30', 'model': MODEL, 'parameters': pilot.parameters(),
              'scope': 'ONE fixed n47 INITIAL closed-rho-box upper-moment route-selection pilot',
              'affinity_mask': 3, 'scale': str(S), 'status': 'in-progress', 'active_stage': 'first-ODE',
              'completed_absolute_terms': {}, 'partial_terms_are_a_complete_bound': False,
              'virtual_sigma_is_not_a_distribution': True, 'actual_rho_ge_sigma_assumed': False,
              'rho_for_all_numerator_prices': str(UPPER_MOMENT),
              'rho_for_final_ratio_denominator': str(RHO_LOWER),
              'existing_true_gamma_root_helper': 'finite_n_closed_rho_box_pilots.RhoBox.gamma',
              'existing_full_sine_helper': 'finite_n_closed_rho_box_pilots.RhoBox.h_complete',
              'gamma_chosen_or_sampled': False, 'sine_caps': 'both retained in full h_complete',
              'CF_source': 'same actual standardized iid law; four raw squared inequalities plus raw Taylor reference',
              'sigma_normalization': {'beta': 'sigma/sqrt(n)', 'v': 'beta*t', 's': 'n/sigma^2',
                                      'd': '1/sigma^2', 'W': 'sigma*H_U(v/sigma)',
                                      'normalized_residual_forcing': 's*W_U(v)',
                                      'pred_spectrum': 'exp((s-d)*G_U(v))',
                                      'core': 's^(3/2)*exp(-s*(v^2-w^2)/2+(s-d)*G_U(w))*W_U(w)',
                                      'Laplace_prefactor_power': '3/2'},
              'new_upper_moment_normalized_and_pred_CF_bridge_Lean_proved': False,
              'new_upper_moment_actual_error_spectral_bridge_Lean_proved': False,
              'new_upper_moment_positive_Laplace_bridge_Lean_proved': False,
              'formal_lean_numerical_theorem': False, 'whole_n47_initial_cell_formally_certified': False,
              'whole_n47_through_212_certified': False, 'complete_classical_formula_claimed': False,
              'min_loss_switch_used': False, 'Taylor_or_triangle_cap_used': False,
              'P6_used': False, 'phase_cap_used': False, 'physical_tail_cap_used': False,
              'old_source_or_result_modified': False}

    def save_part(name: str, term: I, next_stage: str):
        record['completed_absolute_terms'][name] = scalar.base.rational_text(term)
        record['active_stage'] = next_stage
        record['elapsed_seconds_metadata'] = time.monotonic()-started
        atomic_save(args.output, record)

    atomic_save(args.output, record)
    try:
        result = pilot.evaluate(save_part)
    except BaseException as error:
        record.update({'status': 'interrupted' if isinstance(error, KeyboardInterrupt) else 'failed',
                       'error_kind': type(error).__name__, 'error_message': str(error),
                       'elapsed_seconds_metadata': time.monotonic()-started})
        atomic_save(args.output, record)
        raise
    record.update({'status': 'completed', 'active_stage': None, 'evaluation': result,
                   'elapsed_seconds_metadata': time.monotonic()-started})
    atomic_save(args.output, record)
    print(json.dumps({'actual_n': N, 'actual_rho_closed_box': [str(RHO_LOWER), str(UPPER_MOMENT)],
                      'sqrt_n_delta_over_rho_lower_upper': result['sqrt_n_delta_over_rho_lower_upper']['decimal_upper'],
                      'arithmetic_strict_success_given_pending_bridges': result['arithmetic_strict_success_given_pending_bridges'],
                      'new_CF_and_spectral_bridges_Lean_proved': False,
                      'formal_lean_numerical_theorem': False}), flush=True)


if __name__ == '__main__':
    main()
