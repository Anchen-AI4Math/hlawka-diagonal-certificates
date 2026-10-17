"""Small certificate pieces import the shared analytic domain theorems."""
import json
from fractions import Fraction as F
from generate_contractor_lean import ROOT, rat
from generate_real_window_chunks import bounds, hypotheses


def main():
    groups=json.loads((ROOT/'certificates/lean-grouped-geometry.json').read_text(encoding='utf-8'))['groups']
    manifest=[]
    for cutoff in [21,26]:
        profile=json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())
        slabs=json.loads((ROOT/f'certificates/cutoff{cutoff}/contractor.json').read_text())
        number=0
        for gi,g in enumerate(groups):
            members=sorted(r['index'] for r in g['members'] if r['cutoff']==cutoff)
            for start in range(0,len(members),8):
                indices=members[start:start+8]
                assert indices==list(range(indices[0],indices[-1]+1))
                name=f'nonneg_piece{cutoff}_{number:02d}'
                lines=[f'import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group{gi:02d}',
                       'import Hlawka21.PieceTools']
                lines += [f'import Hlawka21.Localized{cutoff}.Slab{k:03d}' for k in indices]
                lines += ['', 'set_option autoImplicit false','set_option maxHeartbeats 40000000',
                          'namespace HlawkaSchatten.DiagonalCutoff21',
                          'open HlawkaSchatten HlawkaSchatten.DiagonalConstruction','',
                          f'theorem {name} (p : ℝ) (hpa : {rat(F(slabs[indices[0]]["a"]))} ≤ p)',
                          f'    (hpb : p ≤ {rat(F(slabs[indices[-1]]["b"]))}) (X : Triple)']
                lines += hypotheses(profile)
                lines += ['    0 ≤ tripleDeficit p (cyclicConstant p) X := by']

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
                        f'have hBx : coordinateBox {bounds(g["box"])} X :=',
                        '  coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
                        f'apply domain_nonneg_group{gi:02d} p (by linarith) (by linarith) X',
                        '· intro j', '  simpa [coordinateBox] using hBx j j',
                        '· intro j i hji','  simpa [coordinateBox, hji] using hBx j i',
                        '· intro j','  exact (hh.1 j).trans (by norm_num)',
                        '· exact hT.le.trans (by norm_num)',
                        '· intro i j k hij hik hjk',
                        f'  exact (show {rat(F(g["J"]))} ≤ {rat(J)} by norm_num).trans (hh.2.2.1 i j k hij hik hjk)',
                        f'· exact (show {rat(F(g["W"]))} ≤ {rat(W)} by norm_num).trans hh.2.2.2.le'])
                emit(indices,'  ')
                lines += ['', 'end HlawkaSchatten.DiagonalCutoff21',
                          f'#print axioms HlawkaSchatten.DiagonalCutoff21.{name}','']
                path=ROOT/f'formalization/Hlawka21/Pieces{cutoff}/Piece{number:02d}.lean'
                path.parent.mkdir(parents=True,exist_ok=True)
                path.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
                manifest.append(dict(cutoff=cutoff,index=number,group=gi,indices=indices,
                                     a=slabs[indices[0]]['a'],b=slabs[indices[-1]]['b'],
                                     module=f'Hlawka21.Pieces{cutoff}.Piece{number:02d}',
                                     theorem=name,source=path.relative_to(ROOT).as_posix()))
                number+=1
    for cutoff,lo,hi,count in [(21,F(21),F(26),160),(26,F(26),F(32),96)]:
        rows=[r for r in manifest if r['cutoff']==cutoff]
        assert [k for r in rows for k in r['indices']]==list(range(count))
        cursor=lo
        for row in rows:
            assert F(row['a'])==cursor<F(row['b']);cursor=F(row['b'])
        assert cursor==hi
    (ROOT/'formalization/real-pieces.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print('Generated',len(manifest),'small pieces covering all 256 original slabs')


if __name__=='__main__':
    main()
