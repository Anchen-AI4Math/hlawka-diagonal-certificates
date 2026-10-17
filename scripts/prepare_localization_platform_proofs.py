"""Isolate actual-norm localization from all analytic theorem imports."""
import argparse
import hashlib
import json
from fractions import Fraction as F
from generate_contractor_lean import ROOT, rat
from prepare_real_chunk_platform_proofs import bundle, HELPER


def prepare(cutoff,index):
    profile=json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())
    slab=json.loads((ROOT/f'certificates/cutoff{cutoff}/contractor.json').read_text())[index]
    coarse,final=profile['coarse_box'],slab['final']['box']
    a,b,c,A,U=map(F,[slab['a'],slab['b'],profile['c'],3*F(profile['q']),slab['final']['U']])
    J=3-U-2/(c*a)-F(profile['coarse_tail']);W=6-F(slab['h'])
    key=f'actual_localize{cutoff}_slab{index:03d}'
    name='HlawkaSchatten.DiagonalCutoff21.'+key
    statement=f'''theorem {name} :
    ∀ p : ℝ, {rat(a)} ≤ p → p ≤ {rat(b)} → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -({coarse['diag_max']} : ℝ) ≤ X i i ∧ X i i ≤ -({coarse['diag_min']} : ℝ)) →
      (∀ j i, j ≠ i → ({coarse['off_min']} : ℝ) ≤ X j i ∧ X j i ≤ ({coarse['off_max']} : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < {rat(A)} →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ({rat(c)}*p) →
      (∀ i, lpNorm p (X i) ≤ {rat(U)}) ∧
      (∀ i, -({final['diag_max']} : ℝ) ≤ X i i ∧ X i i ≤ -({final['diag_min']} : ℝ)) ∧
      (∀ j i, j ≠ i → ({final['off_min']} : ℝ) ≤ X j i ∧ X j i ≤ ({final['off_max']} : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → {rat(J)} ≤ X j i + X k i) ∧
      {rat(W)} < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by sorry'''
    def proof(ns):
        return f''' := by
  intro p hp hpmax X hd ho hS hT hG
  have hB : {ns}.coordinateBox ({coarse['diag_min']} : ℝ) ({coarse['diag_max']} : ℝ)
      ({coarse['off_min']} : ℝ) ({coarse['off_max']} : ℝ) X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [{ns}.coordinateBox] using hd i
    · simpa [{ns}.coordinateBox, hji] using ho j i hji
  have hh := {ns}.localize{cutoff}_slab{index:03d} p hp hpmax X hB hS hT hG
  refine ⟨hh.1, ?_, ?_, hh.2.2.1, hh.2.2.2⟩
  · intro i
    simpa [{ns}.coordinateBox] using hh.2.1 i i
  · intro j i hji
    simpa [{ns}.coordinateBox, hji] using hh.2.1 j i
'''
    preamble,body=bundle(f'Hlawka21.Localized{cutoff}.Slab{index:03d}')
    assert not any(line.startswith('import Theorems.') for line in preamble.splitlines())
    body=body.replace('open HlawkaSchatten.DiagonalCutoff21\n','')
    minimal='\n'.join(line for line in preamble.splitlines() if line.startswith(('import Definitions.','open ')))+'\n'
    source=body+statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',proof(HELPER))+'\n#print axioms solution\n'
    assert 'sorry' not in source
    path=ROOT/f'formalization/platform/Sol_{key}.lean'
    path.write_text(source,encoding='utf-8',newline='\n')
    mirror=f'import Hlawka21.Localized{cutoff}.Slab{index:03d}\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n\n'+statement.replace(' := by sorry',proof('HlawkaSchatten.DiagonalCutoff21'))+f'\n#print axioms {name}\n'
    (ROOT/'formalization/Theorems'/('Thm_'+name.replace('.','_')+'.lean')).write_text(mirror,encoding='utf-8',newline='\n')
    print(key,len(source.encode('utf-8')),'bytes',flush=True)
    return dict(key=key,theorem_name=name,theorem_title=f'Actual norm localization on [{a},{b}]',formal_statement=statement,preamble=minimal,
                natural_language_statement=f'For every real p in [{a},{b}], a coarse-box triple with original singleton norm sum three, total norm below {A}, and original pair-gap sum below 2/(({c})p) obeys the displayed actual singleton norm cap, contracted coordinate box, linear complementary-pair floors and strict off-diagonal-sum floor. Singleton norms need not be equal. This is the actual-norm localization certificate for one parameter slab, with no imported theorem dependencies and no abstract validity predicate.',
                source='Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 3-4, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic contraction framework adapted from @bwdaugherty, Apache-2.0, with original notices retained.',
                tags=['hlawka-schatten','exact-arithmetic','localization'],solution_file=path.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                explanation='No theorem imports are used. The file proves the original finite-coordinate p-norm identities, refined pair-tail bound, the real-norm-to-Facts bridge, all three integer-power root certificates, the logarithmic budget, ten complete contraction rounds and the derived linear pair/offsum floors. The public statement exposes actual original norm data and explicit rational conclusions. This minimal packet isolates finite localization from analytic theorem-import overhead and larger multi-slab files.')


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--cutoff',type=int,choices=[21,26],default=21)
    parser.add_argument('--index',type=int,default=0)
    args=parser.parse_args()
    item=prepare(args.cutoff,args.index)
    path=ROOT/'formalization/platform/localization-proofs.json'
    rows=json.loads(path.read_text(encoding='utf-8')) if path.exists() else []
    rows=[r for r in rows if r['key']!=item['key']]+[item]
    path.write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')


if __name__=='__main__':
    main()
