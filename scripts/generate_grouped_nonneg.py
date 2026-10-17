"""Assemble cyclic-constant nonnegativity on both grouped convex domains."""
import json
from fractions import Fraction as F
from generate_contractor_lean import ROOT, rat


def main():
    data = json.loads((ROOT / 'certificates/lean-grouped-geometry.json').read_text(encoding='utf-8'))
    for i, g in enumerate(data['groups']):
        a, b, U, A, J, W = (rat(F(g[k])) for k in ['a', 'b', 'U', 'A', 'J', 'W'])
        ell, u, v, w = (rat(F(g['box'][k])) for k in ['diag_min', 'diag_max', 'off_min', 'off_max'])
        name = f'grouped_deficit_nonneg{i:02d}'
        source = f'''import Hlawka21.NormDomainNonneg
import Hlawka21.ScalarMilestoneBounds
import Hlawka21.GroupedConvexity.Group{i:02d}

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem {name} (p : ℝ) (hpa : {a} ≤ p) (hpb : p ≤ {b})
    (X : Triple) (hX : X ∈ normCappedDomain p {ell} {u} {v} {w} {U} {A} {J} {W}) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hK := cyclicConstant_bounds_window (p := p) (by linarith) (by linarith)
  exact normDomain_deficit_nonneg_of_convex (by linarith) (by norm_num)
    (by norm_num) (by norm_num)
    (grouped_deficit_convex{i:02d} p (cyclicConstant p) hpa hpb hK.1.le hK.2) hX

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.{name}
'''
        path = ROOT / f'formalization/Hlawka21/GroupedNonneg/Group{i:02d}.lean'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding='utf-8', newline='\n')
        print(path.relative_to(ROOT))


if __name__ == '__main__':
    main()
