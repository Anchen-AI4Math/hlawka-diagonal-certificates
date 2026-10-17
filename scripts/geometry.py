"""Exact constants for the norm-constrained, permutation-invariant domain.

Pure Fraction algebra. Arguments are in docs/proof-21.md and docs/proof-26.md.
"""
from fractions import Fraction as F

def capped_tail(box,total_cap):
    """Tail coordinate = total coordinate - excluded positive off-diagonal."""
    al,ah,bl,bh=[F(box[k]) for k in ['diag_min','diag_max','off_min','off_max']]
    lower=bl-ah
    upper=min(bh-al,total_cap-bl)
    if lower>upper: raise ValueError('inconsistent tail interval')
    return max(abs(lower),abs(upper))

def pair_cap_constants(box,total_cap,norm_cap,epsilon1,epsilon2,pair_floor,offsum_floor):
    """Constants on the convex domain with linear pair and offsum floors."""
    al,ah,bl,bh=[F(box[k]) for k in ['diag_min','diag_max','off_min','off_max']]
    if not (0<al<=ah and 0<bl<=bh and total_cap>0 and norm_cap>0
            and epsilon1>0 and epsilon2>0 and pair_floor>0 and offsum_floor>0):
        raise ValueError('pair-cap geometry domain')
    m,M=min(al,bl),max(ah,bh)
    large=max(2*bl,pair_floor)
    vmin,vmax=large-ah,min(2*bh-al,total_cap)
    tail=capped_tail(box,total_cap)
    average_off_min=max(bl,offsum_floor/6)
    orbit_lower=(al/bh>=F(1,2) or total_cap<=F(3,2)*average_off_min)
    if not (0<vmin<=vmax and 0<tail<=large and orbit_lower and ah/bl<=2):
        raise ValueError('pair-cap signs or orbit range')
    shape=(vmin*vmin+vmax*vmax)/(m*m*(vmin+vmax)**2)
    # ||E|| <= (sqrt(3)+2*rho)||U|| <= (7/4+2*rho)||U||.
    error_coefficient=(F(7,4)+2*tail/large)**2
    gT=4*M*M*(1+epsilon2)*shape*(1+epsilon1)
    gC=4*M*M*(1+epsilon2)*shape*3*(1+1/epsilon1)+error_coefficient*(1+1/epsilon2)
    return dict(m=m,M=M,vmin=vmin,vmax=vmax,tail=tail,large=large,shape=shape,
                pair_floor=pair_floor,offsum_floor=offsum_floor,average_off_min=average_off_min,
                error_coefficient=error_coefficient,gT=gT,gC=gC,
                rT_factor=total_cap/large,rT_base=tail*total_cap/(large*vmin),
                rC_factor=norm_cap/large,rC_base=tail*norm_cap/(large*m))

def constants(box, total_cap, norm_cap, epsilon1, epsilon2):
    al,ah,bl,bh=[F(box[k]) for k in ['diag_min','diag_max','off_min','off_max']]
    if not (0<al<=ah and 0<bl<=bh and total_cap>0 and norm_cap>0 and epsilon1>0 and epsilon2>0):
        raise ValueError('geometry domain')
    m,M=min(al,bl),max(ah,bh)
    vmin,vmax=2*bl-ah,2*bh-al
    tail=max(abs(bl-ah),abs(bh-al)); large=2*bl
    # At the permutation average, 2b-a <= total_cap and b>=bl.
    # Thus a/b >= 2-total_cap/bl; the box alone need not give a/b>=1/2.
    orbit_lower=(al/bh>=F(1,2) or total_cap<=F(3,2)*bl)
    if not (vmin>0 and tail>0 and tail<=large and orbit_lower and ah/bl<=2):
        raise ValueError('geometry signs or orbit range')
    shape=(vmin*vmin+vmax*vmax)/(m*m*(vmin+vmax)**2)
    gT=4*M*M*(1+epsilon2)*shape*(1+epsilon1)
    gC=4*M*M*(1+epsilon2)*shape*3*(1+1/epsilon1)+16*(1+1/epsilon2)
    return dict(m=m,M=M,vmin=vmin,vmax=vmax,tail=tail,large=large,shape=shape,
                gT=gT,gC=gC,rT_factor=total_cap/large,rT_base=tail*total_cap/(large*vmin),
                rC_factor=norm_cap/large,rC_base=tail*norm_cap/(large*m))
