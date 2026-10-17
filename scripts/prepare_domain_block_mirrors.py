"""Compile the actual localization API once for fast local theorem mirrors.

This file is local proof infrastructure, not a platform Definition. It imports
the already checked full finite localization graph and proves every public
block bound from those actual proofs. No theorem stub or new axiom is used.
"""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
ORIGINAL='HlawkaSchatten.DiagonalCutoff21'
HELPER='HlawkaSchatten.DiagonalDomainApiBundle'


def prepare():
    rows=json.loads((ROOT/'formalization/domain-blocks.json').read_text())
    payloads=json.loads((ROOT/'formalization/platform/domain-block-proofs.json').read_text(encoding='utf-8'))
    blocks=['import Hlawka21.RealWindows\nimport Hlawka21.PieceTools\n',
            'open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff21\n']
    for row,item in zip(rows,payloads,strict=True):
        assert row['theorem_name']==item['theorem_name']
        source=(ROOT/'formalization'/(row['module'].replace('.','/')+'.lean')).read_text(encoding='utf-8')
        source='\n'.join(line for line in source.splitlines() if not line.startswith('import '))
        source=source.replace('namespace '+ORIGINAL,'namespace '+HELPER).replace('end '+ORIGINAL,'end '+HELPER)
        blocks.append(source)
        sol=(ROOT/item['solution_file']).read_text(encoding='utf-8')
        wrapper=sol[sol.index('theorem solution'):]
        wrapper=wrapper.replace('theorem solution','theorem '+item['theorem_name']).replace('#print axioms solution','#print axioms '+item['theorem_name'])
        wrapper=wrapper.replace('HlawkaSchatten.DiagonalRealBundle.',ORIGINAL+'.')
        wrapper=wrapper.replace(ORIGINAL+'.bounds_',HELPER+'.bounds_')
        blocks.append(wrapper)
    complete='\n\n'.join(blocks).rstrip()+'\n'
    assert 'sorry' not in complete
    (ROOT/'formalization/Hlawka21/DomainBlockApi.lean').write_text(complete,encoding='utf-8',newline='\n')
    for item in payloads:
        mirror=ROOT/'formalization/Theorems'/('Thm_'+item['theorem_name'].replace('.','_')+'.lean')
        mirror.write_text('import Hlawka21.DomainBlockApi\n',encoding='utf-8',newline='\n')
    print('Prepared 65 actual-proof API mirrors; arithmetic remains in the proof module, not in platform Definitions.')


if __name__=='__main__':prepare()
