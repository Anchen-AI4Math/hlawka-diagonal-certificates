"""Cross-check exact dyadic arithmetic against higher precision Arb enclosures."""
import json
from fractions import Fraction as F
from pathlib import Path
import rational_intervals as r
import intervals as a

r.configure(192); a.ctx.prec=320
count=0
def enclosed(exact,reference):
    global count
    if not (a.Q(exact.lower())<=reference and reference<=a.Q(exact.upper())):
        raise ValueError('Reference enclosure not contained in dyadic result')
    count+=1
for x in ['1/1000000','1/7','1/2','1','3/2','2','3','1000']:
    enclosed(r.Q(x).log(),a.Q(x).log())
for x in ['-100','-32','-3','-1/2','0','1/7','1/2','3','32','100']:
    enclosed(r.Q(x).exp(),a.Q(x).exp())
for x,y in [('1/7','127/4'),('2','32'),('3','4/127'),('1/2','-3/2')]:
    enclosed(r.Q(x)**r.Q(y),a.Q(x)**a.Q(y))
for x,y in [('1/3','-7/5'),('-1/3','-7/5'),('0','1/7')]:
    for op in ['add','sub','mul','truediv']:
        enclosed(getattr(r.Q(x),'__'+op+'__')(r.Q(y)),getattr(a.Q(x),'__'+op+'__')(a.Q(y)))
for p in ['127/4','32']:
    for t in ['1/2','886/1000','1','2']:
        enclosed(r.ratio(r.Q(p),r.Q(t)),a.ratio(a.Q(p),a.Q(t)))
for interval in [('1/7','2/7'),('-2','3'),('-100','-99')]:
    x,y=map(F,interval)
    # Arb stores radii at lower precision and may widen an input interval;
    # compare the monotone endpoint values, not that wider input's image.
    for endpoint in [x,y]:
        enclosed(r.I(x,y).exp(),a.Q(endpoint).exp())
        if x>0: enclosed(r.I(x,y).log(),a.Q(endpoint).log())
try: r.Q(.5)
except TypeError: count+=1
else: raise ValueError('Float accepted')
for bad in [lambda:r.I(-1,1).log(),lambda:r.Q(1)/r.I(-1,1)]:
    try: bad()
    except ValueError: count+=1
    else: raise ValueError('Invalid domain accepted')
result=dict(status='PASS',checks=count,rational_bits=192,reference_arb_bits=320,scope='Arithmetic cross-checks, not a second analytical reviewer')
Path('results/arithmetic-crosscheck.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
