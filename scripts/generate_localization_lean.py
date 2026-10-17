"""Connect each proved contraction schedule to the original coordinate norms."""
import argparse,json
from fractions import Fraction as F
from pathlib import Path
from generate_contractor_lean import ROOT,rat

def generate(cutoff,index,slab,profile):
    a,b,tlo,thia,thib,D,delta,h,q=map(F,(slab[k] for k in ['a','b','tlo','thia','thib','D','delta','h','q']))
    c=F(profile['c']);eps=F(profile['coarse_tail']);A=3*q
    box=profile['coarse_box'];final=slab['final'];fb=final['box'];U=F(final['U'])
    bounds=lambda x:' '.join(rat(x[k]) for k in ['diag_min','diag_max','off_min','off_max'])
    name=f'localize{cutoff}_slab{index:03d}'
    lines=[f'import Hlawka21.Window{cutoff}.Slab{index:03d}',
        'import Hlawka21.LinearFloors','import Mathlib.Analysis.Complex.ExponentialBounds','',
        '/- Original p-norm hypotheses imply all premises of the complete',
        '   contraction schedule. Three rational root certificates are checked',
        '   as integer-power inequalities; no numerical validity predicate',
        '   or abstract Facts hypothesis remains. -/',
        'set_option autoImplicit false','set_option maxHeartbeats 200000000',
        'set_option exponentiation.threshold 2048','',
        'namespace HlawkaSchatten.DiagonalCutoff21',
        'open HlawkaSchatten HlawkaSchatten.DiagonalConstruction','',
        f'theorem {name} (p : ℝ) (hpa : {rat(a)} ≤ p) (hpb : p ≤ {rat(b)}) (X : Triple)',
        f'    (hB : coordinateBox {bounds(box)} X)',
        '    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)',
        f'    (hT : lpNorm p (X 0 + X 1 + X 2) < {rat(A)})',
        f'    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ({rat(c)} * p)) :',
        f'    (∀ i, lpNorm p (X i) ≤ {rat(U)}) ∧ coordinateBox {bounds(fb)} X ∧',
        f'    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →',
        f'      {rat(3-U-2/(c*a)-eps)} ≤ X j i + X k i) ∧',
        f'    {rat(6-h)} < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by',
        '  have hp1 : 1 ≤ p := by linarith',
        f'  have hpc : {cutoff} ≤ p := by linarith',
        f'  have hcrit : 6 * Real.log 2 ≤ 2 / {rat(c)} := by',
        '    have hh := Real.log_two_lt_d9','    norm_num','    linarith',
        f'  have htlo : {rat(tlo)} ≤ (1/2 : ℝ) ^ (1/{rat(a)}) := by',
        f'    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := {rat(tlo)})',
        f'      (by norm_num) {a.denominator} {a.numerator} (by norm_num) (by norm_num)',
        '    norm_num at hh ⊢; exact hh',
        f'  have hthia : (1/2 : ℝ) ^ (1/{rat(a)}) ≤ {rat(thia)} := by',
        f'    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := {rat(thia)})',
        f'      (by norm_num) (by norm_num) {a.denominator} {a.numerator} (by norm_num) (by norm_num)',
        '    norm_num at hh ⊢; exact hh',
        f'  have hthib : (1/2 : ℝ) ^ (1/{rat(b)}) ≤ {rat(thib)} := by',
        f'    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := {rat(thib)})',
        f'      (by norm_num) (by norm_num) {b.denominator} {b.numerator} (by norm_num) (by norm_num)',
        '    norm_num at hh ⊢; exact hh',
        f'  have htail := refined_pair_tail{cutoff} hpc X hB'+(' hT.le' if cutoff==21 else ''),
        f'  have FF : Facts p (cp p) {rat(D)} {rat(delta)} {rat(h)} {rat(A)} {rat(2*thib)} {rat(tlo)} X (fun i ↦ lpNorm p (X i)) := by',
        f'    have facts := facts_of (α := {rat(a)}) (β := {rat(b)}) (c := {rat(c)}) (eps := {rat(eps)})',
        f'      (D := {rat(D)}) (δ := {rat(delta)}) (h := {rat(h)}) (A := {rat(A)})',
        f'      (tlo := {rat(tlo)}) (thia := {rat(thia)}) (thib := {rat(thib)})',
        f'      (ell := {rat(box["diag_min"])}) (u := {rat(box["diag_max"])})',
        f'      (v := {rat(box["off_min"])}) (w := {rat(box["off_max"])})',
        '      (by norm_num) hpa hpb hp1 (by norm_num) hcrit',
        '      (by norm_num) (by norm_num) (by norm_num)',
        '      (by norm_num) htlo hthia hthib',
        '      (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
        '      hB hS hT hG htail',
        '    norm_num at facts','    exact facts',
        '  have hn0 := initial_norm_lower hp1 X hB',
        f'  have hh := contract{cutoff}_slab{index:03d} p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0',
        '  refine ⟨hh.1, hh.2, ?_, ?_⟩',
        '  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail',
        '    norm_num at hj','    exact hj',
        '  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)',
        '    linarith','',
        'end HlawkaSchatten.DiagonalCutoff21','',
        f'#print axioms HlawkaSchatten.DiagonalCutoff21.{name}','']
    path=ROOT/f'formalization/Hlawka21/Localized{cutoff}/Slab{index:03d}.lean'
    path.parent.mkdir(parents=True,exist_ok=True)
    code='\n'.join(lines);assert 'sorry' not in code
    path.write_text(code,encoding='utf-8',newline='\n')
    return path

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--cutoff',type=int,choices=[21,26],default=21)
    parser.add_argument('--start',type=int,default=0);parser.add_argument('--limit',type=int,default=1)
    args=parser.parse_args()
    profile=json.loads((ROOT/f'profiles/cutoff{args.cutoff}.json').read_text(encoding='utf-8'))
    slabs=json.loads((ROOT/f'certificates/cutoff{args.cutoff}/contractor.json').read_text(encoding='utf-8'))
    for index in range(args.start,min(len(slabs),args.start+args.limit)):
        print(generate(args.cutoff,index,slabs[index],profile).relative_to(ROOT),flush=True)
