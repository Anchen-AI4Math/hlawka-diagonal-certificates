"""Record downloaded reference hashes, without reading any credentials."""
import hashlib,json
from pathlib import Path

root=Path('sources')
records=[]
for name in ['coarse32','contract32','convex_box32']:
    meta=json.loads((root/(name+'-submission.json')).read_text(encoding='utf8'))
    records.append(dict(name=name,theorem_id=meta['theorem_id'],submission_id=meta['id'],author=meta['username'],status=meta['status'],accepted_at=meta['accepted_at'],url='https://prove2.me/theorems/'+meta['theorem_id'],local_source=name+'.lean'))
manifest=dict(retrieved_date='2026-10-17',campaign='https://prove2.me/campaigns/sharp-diagonal-hlawka-constant',platform_cutoff='32',main_submission='2d248eb1-4938-4dee-8392-df24d2c70f2f',baseline_repository='https://github.com/savarin/hlawka-schatten',baseline_commit='1829591140522193a81ae721330e4d775c81123e',components=records,independently_compiled=False,files={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.iterdir()) if p.is_file() and p.suffix in ('.json','.lean') and p.name!='provenance.json'})
(root/'provenance.json').write_text(json.dumps(manifest,indent=2)+'\n')
