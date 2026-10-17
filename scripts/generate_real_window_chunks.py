"""Place every actual-norm localization slab in a proved nonnegative domain."""
import hashlib
import json
from fractions import Fraction as F
from generate_contractor_lean import ROOT, rat


def bounds(box):
    return ' '.join(rat(F(box[k])) for k in ['diag_min', 'diag_max', 'off_min', 'off_max'])


def hypotheses(profile):
    return [f'    (hB : coordinateBox {bounds(profile["coarse_box"])} X)',
            '    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)',
            f'    (hT : lpNorm p (X 0 + X 1 + X 2) < {rat(3*F(profile["q"]))})',
            f'    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ({rat(F(profile["c"]))}*p)) :']


def main():
    data = json.loads((ROOT/'certificates/lean-grouped-geometry.json').read_text(encoding='utf-8'))
    for path, digest in data['inputs'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    membership = {}
    for i, group in enumerate(data['groups']):
        for row in group['members']:
            key = (row['cutoff'], row['index'])
            assert key not in membership
            membership[key] = (i, group)
    assert len(membership) == 256
    manifest = []
    for cutoff in [21, 26]:
        profile = json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text(encoding='utf-8'))
        slabs = json.loads((ROOT/f'certificates/cutoff{cutoff}/contractor.json').read_text(encoding='utf-8'))
        cursor = F(profile['p_min'])
        for slab in slabs:
            assert F(slab['a']) == cursor < F(slab['b'])
            assert F(slab['q']) == F(profile['q'])
            cursor = F(slab['b'])
        assert cursor == F(profile['p_max'])
        for chunk, start in enumerate(range(0, len(slabs), 16)):
            indices = list(range(start, min(start+16, len(slabs))))
            name = f'localized_nonneg{cutoff}_chunk{chunk:02d}'
            lines = ['import Hlawka21.NormDomainInclusion']
            lines += [f'import Hlawka21.GroupedNonneg.Group{i:02d}' for i in sorted({membership[cutoff,k][0] for k in indices})]
            lines += [f'import Hlawka21.Localized{cutoff}.Slab{k:03d}' for k in indices]
            lines += ['', '/- Finite interval decisions and all domain inclusions are Lean proofs. -/',
                      'set_option autoImplicit false', 'set_option maxHeartbeats 40000000',
                      'namespace HlawkaSchatten.DiagonalCutoff21',
                      'open HlawkaSchatten HlawkaSchatten.DiagonalConstruction', '',
                      f'theorem {name} (p : ℝ) (hpa : {rat(F(slabs[indices[0]]["a"]))} ≤ p)',
                      f'    (hpb : p ≤ {rat(F(slabs[indices[-1]]["b"]))}) (X : Triple)']
            lines += hypotheses(profile)
            lines += ['    0 ≤ tripleDeficit p (cyclicConstant p) X := by']

            def emit(items, indent, stem='h'):
                if len(items) > 1:
                    mid = len(items)//2
                    boundary = rat(F(slabs[items[mid]]['a']))
                    lines.append(indent+f'rcases le_total p {boundary} with {stem}l | {stem}r')
                    lines.append(indent+'·')
                    emit(items[:mid], indent+'  ', stem+'l')
                    lines.append(indent+'·')
                    emit(items[mid:], indent+'  ', stem+'r')
                    return
                k = items[0]
                i, g = membership[cutoff,k]
                assert F(g['a']) <= F(slabs[k]['a']) < F(slabs[k]['b']) <= F(g['b'])
                group_bounds = bounds(g['box'])
                U,A,J,W = [rat(F(g[key])) for key in ['U','A','J','W']]
                lines.extend(indent+line for line in [
                    f'have hh := localize{cutoff}_slab{k:03d} p (by linarith) (by linarith) X hB hS hT hG',
                    f'have hTA : lpNorm p (X 0 + X 1 + X 2) < {A} := lt_of_lt_of_le hT (by norm_num)',
                    f'have hD : X ∈ normCappedDomain p {group_bounds} {U} {A} {J} {W} :=',
                    '  normDomain_of_localized X hh.1 hh.2.1 hTA hh.2.2.1 hh.2.2.2',
                    '    (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
                    '    (by norm_num) (by norm_num) (by norm_num)',
                    f'exact grouped_deficit_nonneg{i:02d} p (by linarith) (by linarith) X hD'])
            emit(indices, '  ')
            lines += ['', 'end HlawkaSchatten.DiagonalCutoff21',
                      f'#print axioms HlawkaSchatten.DiagonalCutoff21.{name}', '']
            source = ROOT/f'formalization/Hlawka21/Real{cutoff}/Chunk{chunk:02d}.lean'
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text('\n'.join(lines), encoding='utf-8', newline='\n')
            manifest.append(dict(module=f'Hlawka21.Real{cutoff}.Chunk{chunk:02d}',
                                 source=source.relative_to(ROOT).as_posix(), theorem=name,
                                 cutoff=cutoff, start=start, end=indices[-1]+1,
                                 a=slabs[indices[0]]['a'], b=slabs[indices[-1]]['b'],
                                 sha256=hashlib.sha256(source.read_bytes()).hexdigest()))
    (ROOT/'formalization/real-chunks.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print('Generated',len(manifest),'chunks covering all 256 original slabs')


if __name__ == '__main__':
    main()
