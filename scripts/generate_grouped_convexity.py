"""Connect the two exact grouped Hessian certificates to deficit convexity."""
import hashlib
import json
from fractions import Fraction as F
from generate_contractor_lean import ROOT, rat


def main():
    data = json.loads((ROOT / 'certificates/lean-grouped-geometry.json').read_text(encoding='utf-8'))
    for file, digest in data['inputs'].items():
        assert hashlib.sha256((ROOT / file).read_bytes()).hexdigest() == digest
    for i, g in enumerate(data['groups']):
        a, b, c, U, A, J, W = (rat(F(g[k])) for k in ['a', 'b', 'c', 'U', 'A', 'J', 'W'])
        ell, u, v, w = (rat(F(g['box'][k])) for k in ['diag_min', 'diag_max', 'off_min', 'off_max'])
        L, s, t, eta = (rat(F(g['geometry'][k])) for k in ['large', 'vmin', 'vmax', 'tail'])
        name = f'grouped_deficit_convex{i:02d}'
        source = f'''import Hlawka21.NormDomainConvexity
import Hlawka21.GroupedCurvature.Group{i:02d}

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem {name} (p K : ℝ) (hpa : {a} ≤ p) (hpb : p ≤ {b})
    (hKlo : {c}*p ≤ K) (hKhi : K ≤ p/2) :
    ConvexOn ℝ (normCappedDomain p {ell} {u} {v} {w} {U} {A} {J} {W})
      (tripleDeficit p K) := by
  exact normCappedDomain_deficit_convex (L := {L}) (s := {s}) (t := {t}) (eta := {eta})
    (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (grouped_deficit_hessian{i:02d} p K hpa hpb hKlo hKhi)

end HlawkaSchatten.DiagonalCutoff21
#print axioms HlawkaSchatten.DiagonalCutoff21.{name}
'''
        path = ROOT / f'formalization/Hlawka21/GroupedConvexity/Group{i:02d}.lean'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding='utf-8', newline='\n')
        print(path.relative_to(ROOT))


if __name__ == '__main__':
    main()
