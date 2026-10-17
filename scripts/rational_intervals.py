"""Outward dyadic intervals; exp/log proven by finite Taylor sums plus tails.

No Arb, mpmath, Decimal transcendental functions, or floating point arithmetic
is used in certification. See docs/rational-arithmetic.md for error bounds.
"""
from fractions import Fraction as F
from math import factorial
from functools import lru_cache

BITS=256
S=1<<BITS
def configure(bits):
    global BITS,S
    if not 128<=bits<=320: raise ValueError('Supported precision: 128..320 bits')
    BITS=bits; S=1<<bits; log_two.cache_clear()
def ceildiv(a,b): return -((-a)//b)
class Ball:
    __slots__=('lo','hi')
    def __init__(self,lo,hi):
        if lo>hi: raise ValueError('inverted ball')
        self.lo,self.hi=lo,hi
    def __add__(self,other):
        o=Q(other); return Ball(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return Ball(-self.hi,-self.lo)
    def __sub__(self,other): return self+-Q(other)
    def __rsub__(self,other): return Q(other)+-self
    def __mul__(self,other):
        o=Q(other); v=[a*b for a in (self.lo,self.hi) for b in (o.lo,o.hi)]
        return Ball(min(v)//S,ceildiv(max(v),S))
    __rmul__=__mul__
    def __truediv__(self,other):
        o=Q(other)
        if o.lo<=0<=o.hi: raise ValueError('division contains zero')
        lows=[]; highs=[]
        for a in (self.lo,self.hi):
            for b in (o.lo,o.hi):
                lows.append((a*S)//b); highs.append(ceildiv(a*S,b))
        return Ball(min(lows),max(highs))
    def __rtruediv__(self,other): return Q(other)/self
    def __abs__(self):
        if self.lo>=0: return self
        if self.hi<=0: return -self
        return Ball(0,max(-self.lo,self.hi))
    def __pow__(self,other):
        y=Q(other)
        if self.lo==0 and y.lo>0:
            if self.hi==0: return Q(0)
            return Ball(0,(y*Ball(self.hi,self.hi).log()).exp().hi)
        if self.lo<=0: raise ValueError('nonpositive power base')
        return (y*self.log()).exp()
    def __lt__(self,other): return self.hi<Q(other).lo
    def __le__(self,other): return self.hi<=Q(other).lo
    def __gt__(self,other): return self.lo>Q(other).hi
    def __ge__(self,other): return self.lo>=Q(other).hi
    def lower(self): return F(self.lo,S)
    def upper(self): return F(self.hi,S)
    def __str__(self): return '['+str(self.lower())+', '+str(self.upper())+']'
    def union(self,other):
        o=Q(other); return Ball(min(self.lo,o.lo),max(self.hi,o.hi))
    def log(self):
        if self.lo<=0: raise ValueError('log domain')
        a=log_endpoint(self.lo); b=log_endpoint(self.hi)
        return Ball(a.lo,b.hi)
    def exp(self):
        a=Ball(self.lo,self.lo)._exp_point()
        b=Ball(self.hi,self.hi)._exp_point()
        return Ball(a.lo,b.hi)
    def _exp_point(self):
        # Reduce to |z|<=1/2; the signed Taylor polynomial is enclosed termwise.
        k=0; m=max(abs(self.lo),abs(self.hi))
        while m>S//2:
            k+=1; m=ceildiv(m,2)
        z=self/Q(1<<k)
        if max(abs(z.lo),abs(z.hi))>S//2: raise ValueError('exp reduction')
        term=Q(1); total=Q(1)
        for n in range(1,81):
            term=term*z/n; total=total+term
        error=ceildiv(2*S,(1<<81)*factorial(81))
        total=Ball(total.lo-error,total.hi+error)
        if total.lo<=0: raise ValueError('exp positivity')
        for _ in range(k): total=total*total
        return total

def Q(value):
    if isinstance(value,Ball): return value
    if isinstance(value,float): raise TypeError('Float input forbidden')
    f=F(value)
    return Ball((f.numerator*S)//f.denominator,ceildiv(f.numerator*S,f.denominator))
def I(a,b):
    if F(a)>F(b): raise ValueError('inverted interval')
    return Q(a).union(Q(b))
def log_series(m):
    z=(m-1)/(m+1)
    if z.lo<0 or z.hi>S//2: raise ValueError('log reduction')
    zz=z*z; power=z; total=Q(0)
    for j in range(192):
        total=total+power/(2*j+1)
        power=power*zz
    # Tail 2 z^(385)/(385(1-z^2)) <= 8/(3*385*2^385).
    error=ceildiv(8*S,3*385*(1<<385))
    total=2*total
    return Ball(total.lo,total.hi+error)
@lru_cache(maxsize=1)
def log_two(): return log_series(Q(2))
def log_endpoint(v):
    k=v.bit_length()-1-BITS
    if k>=0: m=Ball(v,v)/Q(1<<k)
    else: m=Ball(v,v)*Q(1<<(-k))
    return log_series(m)+k*log_two()

def ratio(p,t):
    # Independent transcription of the seven-norm cyclic quotient.
    single=(t**p+2)**(1/p)
    pair=(2*abs(1-t)**p+Q(2)**p)**(1/p)
    denominator=3*(2*single-pair)
    if not denominator>0: return None
    return (3*single-abs(2-t)*Q(3)**(1/p))/denominator
def envelope(p,q):
    root=((1+q**p)/2)**(1/p)
    if not root<1: return None
    return (1-q)/(2*(1-root))
