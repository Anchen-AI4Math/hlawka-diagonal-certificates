"""Submit the unchanged original real-three goals via the verified reductions."""
import hashlib
import json
from fractions import Fraction as F
from generate_contractor_lean import ROOT, rat


def main():
    chunks = json.loads((ROOT/'formalization/domain-blocks.json').read_text())
    failures = json.loads((ROOT/'formalization/platform/failure-proofs.json').read_text(encoding='utf-8'))
    payloads = []
    ids = {21:'6c62afca-c977-42ef-8cf7-7b8d39ebe08a',26:'a1a7a36f-f8b9-4061-84a2-33080e185b41'}
    for cutoff in [21,26]:
        f = next(r for r in failures if r['key']==f'coarse_failure_window{cutoff}')
        full = (ROOT/f['solution_file']).read_text(encoding='utf-8')
        tail = full[full.index('theorem solution'):].replace('theorem solution','theorem '+f['theorem_name']).replace('#print axioms solution','#print axioms '+f['theorem_name']).replace('HlawkaSchatten.DiagonalFailureBundle','HlawkaSchatten.DiagonalCutoff21')
        mirror = f'import Hlawka21.CoarseFailure{cutoff}\nimport Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_scalar_window{cutoff}\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n\n'+tail
        (ROOT/'formalization/Theorems'/('Thm_'+f['theorem_name'].replace('.','_')+'.lean')).write_text(mirror,encoding='utf-8',newline='\n')
        rows = [r for r in chunks if r['cutoff']==cutoff]
        names = [r['theorem_name'] for r in rows]
        imports = ['import Theorems.Thm_'+f['theorem_name'].replace('.','_')]
        imports += ['import Theorems.Thm_'+name.replace('.','_') for name in names]
        imports += ['import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group'+f'{gi:02d}' for gi in sorted({r['group'] for r in rows})]
        imports += ['import Mathlib.Tactic.Ring','import Mathlib.Tactic.Linarith','import Mathlib.Tactic.NormNum']
        preamble = '\n'.join(imports)+'\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n'
        original = (ROOT/f'platform/proposal/real{cutoff}.lean').read_text(encoding='utf-8')
        statement = original[original.index('theorem '):].strip()
        name = f'HlawkaSchatten.DiagonalCutoff21.real_three_window{cutoff}'
        lines = [preamble,statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',' := by'),
                 '  intro p hp hpmax x y z','  by_contra hn',
                 '  have he : hlawkaDeficit p (cyclicConstant p) x y z =',
                 '      cyclicConstant p * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by',
                 '    unfold hlawkaDeficit pairGapSum pairGap tripleGap','    ring',
                 '  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by',
                 '    rw [he]','    exact sub_neg.mpr (lt_of_not_ge hn)',
                 f'  obtain ⟨X, hd, ho, hS, hT, hG, hfail⟩ := {f["theorem_name"]} p hp hpmax x y z hf',
                 '  norm_num at hT',
                 '  have hnonneg : 0 ≤ tripleDeficit p (cyclicConstant p) X := by']

        def emit(items,indent,prefix='h'):
            if len(items)==1:
                row=items[0]
                target=row['theorem_name']
                lines.append(indent+f'have hh := {target} p (by linarith) (by linarith) X hd ho hS hT hG')
                lines.append(indent+f'exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group{row["group"]:02d} p')
                lines.append(indent+'  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1')
                lines.append(indent+'  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2')
                return
            mid=len(items)//2
            lines.append(indent+f'rcases le_total p {rat(F(items[mid]["a"]))} with {prefix}l | {prefix}r')
            lines.append(indent+'·');emit(items[:mid],indent+'  ',prefix+'l')
            lines.append(indent+'·');emit(items[mid:],indent+'  ',prefix+'r')
        emit(rows,'    ')
        lines += ['  exact (not_lt_of_ge hnonneg) hfail','','#print axioms solution','']
        path=ROOT/f'formalization/platform/Sol_real_three_window{cutoff}.lean'
        path.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
        (ROOT/'formalization/Theorems'/('Thm_'+name.replace('.','_')+'.lean')).write_text('import Hlawka21.RealWindows\n',encoding='utf-8')
        payloads.append(dict(key=f'real_three_window{cutoff}',theorem_id=ids[cutoff],theorem_name=name,
                             solution_file=path.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                             explanation='The unchanged unrestricted real-three theorem follows by contradiction. Arbitrary-failure localization gives the coarse box and original norm normalization, total-norm bound and pair-gap bound. A balanced split over the complete finite interval cover applies a four-slab actual-norm localization block, then the shared analytic domain theorem gives nonnegative deficit, contradicting strict failure. All input triples are unrestricted, including zero and unequal singleton norms. All imported theorem dependencies are tracked; the target is not imported. Full closure requires every localization block and analytic dependency to be Proved.'))
    (ROOT/'formalization/platform/real-window-proofs.json').write_text(json.dumps(payloads,indent=2)+'\n',encoding='utf-8')
    print('Prepared both unchanged original real-three goals and actual-proof dependency mirrors.')


if __name__ == '__main__':
    main()
