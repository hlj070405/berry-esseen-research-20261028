"""2026-10-30: original INITIAL47 collector with explicit result-directory IO.
Mathematical assembly is unchanged; collect() performs no writes.
"""
from fractions import Fraction as F
import argparse
import json
from math import ceil
from pathlib import Path
import upper_moment_sine_nodes as engine

def rho_left(i):
    return F(1)+F(3361,4000)*F(i,24)

def envelope(r):
    return min(F(469,1000),F(1661,5000)*(1+F(429,1000)/r),
               F(3031,10000)*(1+F(323,500)/r))

def exact_value(piece):
    return F(int(piece['upper_numerator']),int(piece['denominator']))

def check_entry(data,row,left,right,A,ctx,point=False):
    values = []
    endpoints = (left,) if point else (left,right)
    assert len(row['endpoint_keys'])==len(endpoints)
    for nu,key in zip(endpoints,row['endpoint_keys']):
        value = data['completed_prices'][key]
        engine.UpperMomentSineEvaluator(A,context=ctx).validate(value)
        assert value['parameters']==engine.physical_parameters(nu,A,context=ctx)
        values.append(engine.score(value))
    theta = F(0) if point else F(3,2)*(right-left)**2/(8*left**2)
    assert 0<=theta<1
    if not point:
        assert F(row['theta'])==theta and F(row['factor'])==1/(1-theta)
    comparison = max(values)/(1-theta)
    saved = row.get('comparison_upper',row.get('joint_upper'))
    assert exact_value(saved)==comparison<ctx.target
    return comparison

def collect(results_dir: Path) -> dict:
    remaining = json.loads((results_dir/'upper_moment_initial47_remaining.json').read_text(encoding='utf-8'))

    last = json.loads((results_dir/'upper_moment_initial47_completion.json').read_text(encoding='utf-8'))

    assert not remaining['terminal_failure'] and not last['terminal_failure']

    ce_up = F(409733,1000000)

    assert ce_up+F(3,10)/47 < F(4247,10000)

    assert all(ce_up+F(3,10)/47 < envelope(rho_left(i)) for i in range(20))

    cases, node_count, point_count = [],0,0

    for i,K in ((20,48),(21,66),(22,101),(23,213)):
        L,U = rho_left(i),rho_left(i+1)
        target = envelope(L)
        assert target==F(1661,5000)*(1+F(429,1000)/L)
        assert ceil(F(3,10)/(target-ce_up))==K
        assert ce_up+F(3,10)/K<=target
        ctx = engine.UpperMomentContext(U=U,rhoLower=L,target=target)
        if i<23:
            data = remaining
            rows = [row for row in data['proved_entries'] if row['entry']['i']==i]
        else:
            data,rows = last,last['proved_nodes']
        intervals,comparisons = [],[]
        for row in rows:
            raw = row['entry'] if i<23 else row['node']
            point = raw.get('kind')=='point'
            left = F(raw['nu']) if point else F(raw['nu_left'])
            right = left if point else F(raw['nu_right'])
            A = F(raw['A'])
            comparison = check_entry(data,row,left,right,A,ctx,point)
            intervals.append((left,right)); comparisons.append(comparison)
            point_count += point
            node_count += not point
        intervals.sort()
        if K==48:
            assert intervals==[(F(47),F(47))]
        else:
            cursor = F(47)
            for left,right in intervals:
                assert left==cursor<right
                cursor = right
            assert cursor==K-1
        cases.append({'i':i,'rho_closed_box':[str(L),str(U)],
                      'CF_actual_n_band':[47,K-1],'Gaussian_from_actual_n':K,
                      'target':str(target),'CF_comparison_uppers':list(map(str,comparisons)),
                      'CF_nu_cover':[[str(a),str(b)] for a,b in intervals]})

    assert node_count==14 and point_count==1

    pair_count = sum(K-47 for K in (48,66,101,213))

    assert pair_count==240

    result = {'date':'2026-10-30','original_actual_n_domain':'all integers n>=47',
              'original_rho_closed_domain':['1','7361/4000'],
              'requires_sharp_all_law_predecessor':True,
              'Gaussian_Lean_source':'BerryEsseen.GaussianInitialMask',
              'actual_CF_CDF_profile_Lean_source':'BerryEsseen.UpperMomentSpectrumPrice',
              'fixed_cap_paid':'4247/10000','Gaussian_masks_cells_0_through_19':True,
              'cases':cases,'finite_CF_index_cell_pairs':pair_count,
              'nondegenerate_CF_nodes':node_count,'single_integer_points':point_count,
              'all_classical_INITIAL47_own_score_inputs_replaced_in_real_arithmetic':True,
              'source_failed_chord_retained':last['source_failed_parent_preserved'],
              'independent_whole_join_review_completed':False,
              'original_support_or_charged_premises_eliminated':False,
              'entire_INITIAL47_certificate_newly_proved':False,
              'formal_lean_numerical_prices':False,'full_conjecture_Lean_proved':False}

    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results-dir', type=Path, default=Path(__file__).resolve().parents[1]/'saved')
    args = parser.parse_args()
    output = args.results_dir/'join_initial47_own_score.json'
    assert not output.exists(), 'Existing results are read-only.'
    result = collect(args.results_dir)
    output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'classical_INITIAL47_own_score_replaced': True,
                      'finite_CF_pairs': 240, 'nodes': 14, 'points': 1,
                      'other_original_premises_preserved': True, 'Lean_numeric_cover': False}), flush=True)


if __name__ == '__main__':
    main()
