"""Group actual-norm localization, without importing analytic theorems.

The conclusions are the explicit bounds of one already proved analytic domain.
Every original parameter slab occurs exactly once. All local dependency mirrors
contain actual proofs, including the arithmetic, rather than theorem stubs.
"""
import hashlib
import json
from fractions import Fraction as F
from generate_contractor_lean import ROOT, rat
from generate_real_window_chunks import bounds, hypotheses
from prepare_real_chunk_platform_proofs import bundle, HELPER


def main():
    groups=json.loads((ROOT/'certificates/lean-grouped-geometry.json').read_text())['groups']
    payloads=[]
    cover=[]
    for cutoff in [21,26]:
        profile=json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())
        slabs=json.loads((ROOT/f'certificates/cutoff{cutoff}/contractor.json').read_text())
        number=0
        for gi,g in enumerate(groups):
            members=sorted(r['index'] for r in g['members'] if r['cutoff']==cutoff)
            for start in range(0,len(members),4):
                indices=members[start:start+4]
                assert indices==list(range(indices[0],indices[-1]+1))
                key=f'localized_domain4_{cutoff}_{number:02d}'
                name='HlawkaSchatten.DiagonalCutoff21.'+key
                a,b=F(slabs[indices[0]]['a']),F(slabs[indices[-1]]['b'])
                box=g['box']
                conclusion=f'''(∀ j, -({box['diag_max']} : ℝ) ≤ X j j ∧ X j j ≤ -({box['diag_min']} : ℝ)) ∧
      (∀ j i, j ≠ i → ({box['off_min']} : ℝ) ≤ X j i ∧ X j i ≤ ({box['off_max']} : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ {rat(F(g['U']))}) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → {rat(F(g['J']))} ≤ X j i + X k i) ∧
      {rat(F(g['W']))} ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1'''
                localname='bounds_'+key
                lines=['import Hlawka21.PieceTools']
                lines += [f'import Hlawka21.Localized{cutoff}.Slab{k:03d}' for k in indices]
                lines += ['', 'set_option autoImplicit false', 'set_option maxHeartbeats 200000000',
                          'namespace HlawkaSchatten.DiagonalCutoff21',
                          'open HlawkaSchatten HlawkaSchatten.DiagonalConstruction','',
                          f'theorem {localname} (p : ℝ) (hpa : {rat(a)} ≤ p)',
                          f'    (hpb : p ≤ {rat(b)}) (X : Triple)']
                lines += hypotheses(profile)
                lines += ['    '+conclusion+' := by']

                def emit(items,indent,prefix='h'):
                    if len(items)>1:
                        mid=len(items)//2
                        lines.append(indent+f'rcases le_total p {rat(F(slabs[items[mid]]["a"]))} with {prefix}l | {prefix}r')
                        lines.append(indent+'·');emit(items[:mid],indent+'  ',prefix+'l')
                        lines.append(indent+'·');emit(items[mid:],indent+'  ',prefix+'r')
                        return
                    k=items[0];slab=slabs[k];U=F(slab['final']['U'])
                    J=3-U-2/(F(profile['c'])*F(slab['a']))-F(profile['coarse_tail'])
                    W=6-F(slab['h'])
                    lines.extend(indent+line for line in [
                        f'have hh := localize{cutoff}_slab{k:03d} p (by linarith) (by linarith) X hB hS hT hG',
                        f'have hBx : coordinateBox {bounds(box)} X :=',
                        '  coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
                        'refine ⟨?_, ?_, ?_, ?_, ?_⟩',
                        '· intro j','  simpa [coordinateBox] using hBx j j',
                        '· intro j i hji','  simpa [coordinateBox, hji] using hBx j i',
                        '· intro j','  exact (hh.1 j).trans (by norm_num)',
                        '· intro i j k hij hik hjk',
                        f'  exact (show {rat(F(g["J"]))} ≤ {rat(J)} by norm_num).trans (hh.2.2.1 i j k hij hik hjk)',
                        f'· exact (show {rat(F(g["W"]))} ≤ {rat(W)} by norm_num).trans hh.2.2.2.le'])
                emit(indices,'  ')
                lines += ['', 'end HlawkaSchatten.DiagonalCutoff21','']
                module=f'Hlawka21.DomainBlocks{cutoff}.Block{number:02d}'
                path=ROOT/'formalization'/(module.replace('.','/')+'.lean')
                path.parent.mkdir(parents=True,exist_ok=True)
                path.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
                coarse=profile['coarse_box'];A=rat(3*F(profile['q']));c=rat(F(profile['c']))
                statement=f'''theorem {name} :
    ∀ p : ℝ, {rat(a)} ≤ p → p ≤ {rat(b)} → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -({coarse['diag_max']} : ℝ) ≤ X i i ∧ X i i ≤ -({coarse['diag_min']} : ℝ)) →
      (∀ j i, j ≠ i → ({coarse['off_min']} : ℝ) ≤ X j i ∧ X j i ≤ ({coarse['off_max']} : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < {A} →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ({c}*p) →
      {conclusion} := by sorry'''

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
  exact {ns}.{localname} p hp hpmax X hB hS hT hG
'''
                preamble,body=bundle(module)
                assert not any(line.startswith('import Theorems.') for line in preamble.splitlines())
                body=body.replace('open HlawkaSchatten.DiagonalCutoff21\n','')
                minimal='\n'.join(line for line in preamble.splitlines() if line.startswith(('import Definitions.','open ')))+'\n'
                source=body+statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',proof(HELPER))+'\n#print axioms solution\n'
                assert 'sorry' not in source
                sol=ROOT/f'formalization/platform/Sol_{key}.lean'
                sol.write_text(source,encoding='utf-8',newline='\n')
                mirror=f'import {module}\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n\n'+statement.replace(' := by sorry',proof('HlawkaSchatten.DiagonalCutoff21'))+f'\n#print axioms {name}\n'
                (ROOT/'formalization/Theorems'/('Thm_'+name.replace('.','_')+'.lean')).write_text(mirror,encoding='utf-8',newline='\n')
                payloads.append(dict(key=key,theorem_name=name,theorem_title=f'Actual norm localization block [{a},{b}]',
                    formal_statement=statement,preamble=minimal,
                    natural_language_statement=f'For every real p in [{a},{b}], coarse-box original norm data with singleton norm sum three, total norm below {3*F(profile["q"])}, and pair-gap sum below 2/(({profile["c"]})p) imply the explicit norm cap and linear bounds of analytic domain {gi}. This block covers {len(indices)} consecutive certified slabs. Unequal singleton norms are allowed.',
                    source='Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 3-4, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic contraction framework adapted from @bwdaugherty, Apache-2.0; notices retained.',
                    tags=['hlawka-schatten','localization','exact-arithmetic'],solution_file=sol.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(sol.read_bytes()).hexdigest(),
                    explanation='No platform theorem imports are used. The complete original norm bridge, rational root inequalities, budget and all ten contraction rounds are proved for at most four slabs, then weakened by exact rational comparisons to a common analytic domain. A balanced interval split covers all real exponents in the block. The analytic theorem is deliberately separated from finite localization; no external validity assumption is introduced.'))
                cover.append(dict(cutoff=cutoff,index=number,group=gi,indices=indices,a=str(a),b=str(b),theorem_name=name,module=module))
                number+=1
    for cutoff,lo,hi,count in [(21,F(21),F(26),160),(26,F(26),F(32),96)]:
        rows=[r for r in cover if r['cutoff']==cutoff]
        assert [i for r in rows for i in r['indices']]==list(range(count))
        cursor=lo
        for r in rows:
            assert F(r['a'])==cursor<F(r['b']);cursor=F(r['b'])
        assert cursor==hi
    (ROOT/'formalization/domain-blocks.json').write_text(json.dumps(cover,indent=2)+'\n',encoding='utf-8')
    (ROOT/'formalization/platform/domain-block-proofs.json').write_text(json.dumps(payloads,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print('Prepared',len(payloads),'domain localization blocks covering all 256 original slabs.')
    from prepare_domain_block_mirrors import prepare
    prepare()


if __name__=='__main__':main()
