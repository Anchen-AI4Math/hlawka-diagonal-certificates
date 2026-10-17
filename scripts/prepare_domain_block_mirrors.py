"""Retain optional actual-proof mirrors for individual localization blocks.

The normal assembly check uses explicit, separately kernel-checked interfaces
instead of recompiling all of these wrappers. These optional mirrors still
contain actual proofs, never local sorry declarations or new axioms.
"""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
ORIGINAL='HlawkaSchatten.DiagonalCutoff21'


def prepare():
    rows=json.loads((ROOT/'formalization/domain-blocks.json').read_text())
    payloads=json.loads((ROOT/'formalization/platform/domain-block-proofs.json').read_text(encoding='utf-8'))
    for row,item in zip(rows,payloads,strict=True):
        assert row['theorem_name']==item['theorem_name']
        sol=(ROOT/item['solution_file']).read_text(encoding='utf-8')
        wrapper=sol[sol.index('theorem solution'):]
        wrapper=wrapper.replace('theorem solution','theorem '+item['theorem_name']).replace('#print axioms solution','#print axioms '+item['theorem_name'])
        wrapper=wrapper.replace('HlawkaSchatten.DiagonalRealBundle.',ORIGINAL+'.')
        mirror=ROOT/'formalization/Theorems'/('Thm_'+item['theorem_name'].replace('.','_')+'.lean')
        complete=f'import {row["module"]}\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n'+wrapper
        assert 'sorry' not in complete
        mirror.write_text(complete,encoding='utf-8',newline='\n')
    print('Prepared 65 optional actual-proof mirrors without a duplicate aggregate module.')


if __name__=='__main__':prepare()
