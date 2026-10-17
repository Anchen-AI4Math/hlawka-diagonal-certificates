"""Small Arb arithmetic layer. Inputs are exact rational strings."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'.deps'))
from fractions import Fraction as F
from flint import arb,ctx
ctx.prec=192
def Q(x):
    x=F(x); return arb(x.numerator)/x.denominator
def I(a,b): return Q(a).union(Q(b))
def abs_power(x,p):
    base=abs(x)
    if base.lower()<=0 and p>0:
        # abs(x) is mathematically nonnegative; Arb's symmetric ball can
        # slightly straddle zero. Use monotonicity in the base explicitly.
        if base.upper()==0: return Q(0)
        return Q(0).union(base.upper()**p)
    return base**p
def ratio(p,t):
    a=(t**p+2)**(1/p)
    b=(2*abs_power(1-t,p)+Q(2)**p)**(1/p)
    den=6*a-3*b
    if not den>0: return None
    return (3*a-Q(3)**(1/p)*abs(2-t))/den
def envelope(p,q):
    den=2*(1-((1+q**p)/2)**(1/p))
    if not den>0: return None
    return (1-q)/den
def require(x,msg):
    if not x: raise ValueError(msg)
