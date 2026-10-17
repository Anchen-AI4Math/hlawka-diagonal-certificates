"""Assemble the unchanged unrestricted real-three window declarations."""
import json
from fractions import Fraction as F
from generate_contractor_lean import ROOT, rat


def main():
    rows = json.loads((ROOT/'formalization/real-chunks.json').read_text())
    lines = ['import Hlawka21.CoarseFailure21','import Hlawka21.CoarseFailure26']
    lines += ['import '+r['module'] for r in rows]
    lines += ['', '/- Arbitrary original failures reduce to the already checked localized chunks.',
              '   The input triples have no norm, sign, nonzero or coordinate restrictions. -/',
              'set_option autoImplicit false','set_option maxHeartbeats 8000000',
              'namespace HlawkaSchatten.DiagonalCutoff21',
              'open HlawkaSchatten HlawkaSchatten.DiagonalConstruction','']
    for cutoff in [21,26]:
        upper = 26 if cutoff == 21 else 32
        profile = json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())
        q = rat(F(profile['q']))
        subset = [r for r in rows if r['cutoff'] == cutoff]
        lines += [f'theorem real_three_window{cutoff} :',
                  f'    ∀ p : ℝ, {cutoff} ≤ p → p ≤ {upper} →',
                  '      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ)',
                  '        (cyclicConstant p) := by',
                  '  intro p hp hpmax x y z','  by_contra hn',
                  '  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by',
                  '    rw [hlawkaDeficit_eq]','    exact sub_neg.mpr (lt_of_not_ge hn)',
                  f'  have hs := scalar_window{cutoff} p hp hpmax',
                  f'  obtain ⟨X, hB, hS, hT, hG, hfail⟩ := coarse_failure{cutoff}',
                  '    hp hs.1 (by norm_num) (by norm_num) hs.2.2 x y z hf',
                  '  norm_num at hT',
                  '  have hnonneg : 0 ≤ tripleDeficit p (cyclicConstant p) X := by']

        def emit(items, indent, prefix='h'):
            if len(items) == 1:
                lines.append(indent+f'exact {items[0]["theorem"]} p (by linarith) (by linarith) X hB hS hT hG')
                return
            mid = len(items)//2
            lines.append(indent+f'rcases le_total p {rat(F(items[mid]["a"]))} with {prefix}l | {prefix}r')
            lines.append(indent+'·')
            emit(items[:mid],indent+'  ',prefix+'l')
            lines.append(indent+'·')
            emit(items[mid:],indent+'  ',prefix+'r')
        emit(subset,'    ')
        lines += ['  exact (not_lt_of_ge hnonneg) hfail','']
    lines += ['end HlawkaSchatten.DiagonalCutoff21',
              '#print axioms HlawkaSchatten.DiagonalCutoff21.real_three_window21',
              '#print axioms HlawkaSchatten.DiagonalCutoff21.real_three_window26','']
    path = ROOT/'formalization/Hlawka21/RealWindows.lean'
    path.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
    print(path.relative_to(ROOT))


if __name__ == '__main__':
    main()
