"""Connect the two exact LP stages using the original norm and proved tails."""
import json
from fractions import Fraction as F
from pathlib import Path
from coarse_lp import model,add,scale,X,P
from generate_coarse_lean import rat,linear

ROOT=Path(__file__).resolve().parents[1]
for cutoff in [21,26]:
    profile=json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())
    lo,c,q,loss=map(F,(profile[k] for k in ['p_min','c','q','orientation_loss']))
    box=profile['coarse_box'];ell,u,v,w=map(F,(box[k] for k in ['diag_min','diag_max','off_min','off_max']))
    A,b,E,f=model(lo,c,q,loss)
    lines=[f'import Hlawka21.Coarse{cutoff}','import Hlawka21.NormBasic',
        'import Hlawka21.ContractionFacts','import Hlawka21.Tail','',
        '/- Paper Section 3: LP stage 0, actual norm half-tail, LP stage 1.',
        '   The hypotheses describe an oriented normalized failure, with',
        '   original coordinate norms throughout. No LP certificate predicate',
        '   or assumed coarse box appears in the hypotheses. -/',
        'set_option autoImplicit false','set_option maxHeartbeats 4000000','',
        'namespace HlawkaSchatten.DiagonalCutoff21',
        'open HlawkaSchatten.DiagonalConstruction','',
        f'theorem coarse_box{cutoff}_oriented (p : ℝ) (hp : {rat(lo)} ≤ p) (X : Triple)',
        '    (N P : Fin 3 → ℝ) (T : ℝ)',
        '    (hNdef : ∀ i, N i = lpNorm p (X i))',
        '    (hP0 : P 0 = lpNorm p (X 1 + X 2))',
        '    (hP1 : P 1 = lpNorm p (X 0 + X 2))',
        '    (hP2 : P 2 = lpNorm p (X 0 + X 1))',
        '    (hTdef : T = lpNorm p (X 0 + X 1 + X 2))',
        '    (hS : N 0 + N 1 + N 2 = 3) (hNT : ∀ i, N i ≤ T)',
        f'    (hT1 : 1 ≤ T) (hTcap : T ≤ {rat(3*q)})',
        f'    (hmain0 : P 0 - (X 1 0 + X 2 0) ≤ {rat(loss)})',
        f'    (hmain1 : P 1 - (X 0 1 + X 2 1) ≤ {rat(loss)})',
        f'    (hmain2 : P 2 - (X 0 2 + X 1 2) ≤ {rat(loss)})',
        f'    (hfail : T - {rat(c*lo)} * (P 0 + P 1 + P 2) ≤ 3 - 6 * {rat(c*lo)}) :',
        f'    coordinateBox {rat(ell)} {rat(u)} {rat(v)} {rat(w)} X := by',
        '  have hp1 : 1 ≤ p := by linarith',
        '  have hpn : 0 < p := by linarith',
        '  have hp21 : 21 ≤ p := by linarith',
        '  have hnpos (i : Fin 3) : 0 ≤ N i := by rw [hNdef]; exact lpNorm_nonneg p (X i)',
        '  have hcoord (j i : Fin 3) : -N j ≤ X j i ∧ X j i ≤ N j := by',
        '    have hc := norm_apply_le_lpNorm hp1 (X j) i',
        '    rw [Real.norm_eq_abs, ← hNdef] at hc',
        '    exact abs_le.mp hc']
    for j in range(3):
        lines.append(f'  have hn{j} := hnpos {j}')
        for i in range(3):lines.append(f'  rcases hcoord {j} {i} with ⟨hx{j}{i}l, hx{j}{i}u⟩')
    for i in range(3):
        lines.extend([f'  have hnt{i} := hNT {i}',
            f'  have ht{i} := norm_apply_le_lpNorm hp1 (X 0 + X 1 + X 2) {i}',
            f'  rw [Real.norm_eq_abs, ← hTdef] at ht{i}',
            f'  simp only [Pi.add_apply] at ht{i}',
            f'  rcases abs_le.mp ht{i} with ⟨ht{i}l, ht{i}u⟩'])
    for i in range(3):
        j,k=[j for j in range(3) if j!=i]
        lines.extend([f'  have hp{i}n : 0 ≤ P {i} := by rw [hP{i}]; exact lpNorm_nonneg p _',
            f'  have hp{i}u : P {i} ≤ N {j} + N {k} := by rw [hP{i}, hNdef, hNdef]; exact lpNorm_add hp1 _ _'])
    values=[f'X {j} {i}' for j in range(3) for i in range(3)]+[f'N {i}' for i in range(3)]+[f'P {i}' for i in range(3)]+['T']
    lines.append('  let v : Fin 16 → ℝ := fun z ↦ match z.val with')
    lines.extend(f'    | {i} => {value}' for i,value in enumerate(values))
    lines.append('    | _ => 0')
    witnesses=['hn0','hnt0','hn1','hnt1','hn2','hnt2','hT1','hTcap']
    witnesses += [f'hx{j}{i}{side}' for j in range(3) for i in range(3) for side in ['l','u']]
    for i in range(3):witnesses += [f'ht{i}l',f'ht{i}u',f'hp{i}n',f'hp{i}u',f'hmain{i}']
    witnesses += ['hfail']
    assert len(witnesses)==len(A)
    for i,(row,bound,witness) in enumerate(zip(A,b,witnesses)):
        lines.append(f'  have h{i} : {linear(row)} ≤ {rat(bound)} := by norm_num [v]; linarith only [{witness}]')
    lines.extend([f'  have heq : {linear(E[0])} = {rat(f[0])} := by norm_num [v]; linarith only [hS]',
        f'  have first := coarse{cutoff}_stage0 v '+' '.join(f'h{i}' for i in range(len(A)))+' heq',
        '  norm_num [v] at first',
        '  rcases first with ⟨'+', '.join(f'a{i}' for i in range(18))+'⟩'])
    for i in range(3):
        j,k=[j for j in range(3) if j!=i]
        lines.extend([f'  have tail{i} : P {i} ≤ X {j} {i} + X {k} {i} + 1/100000 := by',
            f'    rw [hP{i}, lpNorm_eq3 p _ (i := {i}) (j := {j}) (k := {k}) (by decide) (by decide) (by decide)]',
            '    simp only [Pi.add_apply]',
            f'    apply half_tail21 hp21 (by linarith only [a{6*i}]) (by linarith only [a{6*i+1}])',
            f'      (abs_le.mpr ⟨by linarith only [a{6*i+3}], by linarith only [a{6*i+2}]⟩)',
            f'      (abs_le.mpr ⟨by linarith only [a{6*i+5}], by linarith only [a{6*i+4}]⟩)'])
    for i in range(3):
        js=[j for j in range(3) if j!=i]
        A.append(add(P[i],*(scale(X[j][i],-1) for j in js)));b.append(F(profile['half_tail']))
        lines.append(f'  have h{42+i} : {linear(A[-1])} ≤ {rat(b[-1])} := by norm_num [v]; linarith only [tail{i}]')
    lines.extend([f'  have second := coarse{cutoff}_stage1 v '+' '.join(f'h{i}' for i in range(len(A)))+' heq',
        '  norm_num [v] at second',
        '  rcases second with ⟨'+', '.join(f'b{i}' for i in range(18))+'⟩',
        '  intro j i','  fin_cases j <;> fin_cases i'])
    for j in range(3):
        for i in range(3):
            idx=2*(3*j+i)
            if j==i:
                lines.extend(['  · rw [if_pos rfl]',
                    f'    change -{rat(u)} ≤ X {j} {i} ∧ X {j} {i} ≤ -{rat(ell)}'])
            else:
                lines.append(f'  · change {rat(v)} ≤ X {j} {i} ∧ X {j} {i} ≤ {rat(w)}')
            lines.append(f'    constructor <;> linarith only [b{idx}, b{idx+1}]')
    lines.extend(['', 'end HlawkaSchatten.DiagonalCutoff21','',
        f'#print axioms HlawkaSchatten.DiagonalCutoff21.coarse_box{cutoff}_oriented',''])
    path=ROOT/f'formalization/Hlawka21/CoarseConnection{cutoff}.lean'
    path.write_text('\n'.join(lines),encoding='utf-8')
    print('Generated',path.name,flush=True)
