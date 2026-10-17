## Motivation

A norm measures the size of a vector. The triangle inequality says that adding two vectors cannot increase their size beyond the sum of their sizes. The **Hlawka constant problem** asks for a quantitative comparison between the deficit in a three-vector triangle inequality and the sum of the deficits in the three two-vector inequalities. For operator norms, the comparison constant must work in every matrix dimension. Audenaert and Kittaneh state this question in Section 8.2, Problem 7 of [Problems and Conjectures in Matrix and Operator Inequalities](https://arxiv.org/abs/1201.5232v3).

This mission concerns the diagonal, or commuting, case. For a complex diagonal matrix, its Schatten p-norm equals the coordinate p-norm of its diagonal. An exact answer in this setting identifies a concrete extremal family while preserving the requirement that the constant work in every finite dimension. It does not settle the sharp constant for arbitrary noncommuting matrices.

The [foundation mission](https://prove2.me/missions/Sharp_diagonal_Hlawka_constants%3A_foundation_and_proved_cutoff_256) formalizes the cyclic formula for real exponents at least 256. The [accepted cutoff-32 theorem](https://prove2.me/theorems/6e8430ce-7c32-4b82-9a1b-d7fcd67fdeb3), recorded on 16 October 2026, lowers that threshold. The present source is Yuxuan Xu's AI-assisted [research preprint](https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/paper/main.pdf), which supplies a computer-assisted argument extending the formula to all real exponents at least 21. The preprint has not undergone independent analytic review. Its new interval has numerical verification reports but no Lean proof.

## Setting

For a real exponent p greater than one and a finite complex vector x, define the **coordinate p-norm** by

$$N_p(x)=\left(\sum_i |x_i|^p\right)^{1/p}.$$

For three vectors x, y, and z in the same dimension, set

$$S=N_p(x)+N_p(y)+N_p(z),\qquad T=N_p(x+y+z),$$
$$P=N_p(x+y)+N_p(x+z)+N_p(y+z),\qquad G=2S-P.$$

The quantity S minus T is the **triple deficit**. The quantity G is the sum of the three **pair deficits** and is nonnegative by the triangle inequality. A real number C is a **uniform Hlawka constant** when

$$S-T\le C G$$

for all triples and all finite complex dimensions. No equal-norm or nonzero-vector restriction is part of this property.

The candidate sharp constant is specified by an explicit scalar formula. For a real parameter t in the closed interval from one half to two, let

$$A_p(t)=(t^p+2)^{1/p},\qquad B_p(t)=(2|1-t|^p+2^p)^{1/p},$$
$$R_p(t)=\frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)},\qquad K_p=\sup_{1/2\le t\le2}R_p(t).$$

The ratio comes from the cyclic triple (-t,1,1), (1,-t,1), and (1,1,-t). In the exponent range of the mission its denominator is positive, and continuity makes the supremum an attained maximum. The mission imports the campaign's existing definitions of these quantities.

## Formalization targets

The goal is Theorem 1.1 of the source preprint, in the campaign's exact statement format:

$$\forall p\in\mathbb R,\quad 21\le p\ \Longrightarrow\ K_p=\min\{C\in\mathbb R:\ \forall n\in\mathbb N,\ S-T\le C G\text{ on }\mathbb C^n\}.$$

Here the minimum notation includes both admissibility and leastness; existence of an admissible constant is part of the conclusion. The theorem does not assume that certificate validation, localization, or convexity already holds. It does not assert that 21 is the smallest possible exponent threshold.

Four supporting targets follow the source's two finite windows. Equation (7) and Table 1 give, on each full real interval, the scalar inequalities

$$cp<K_p\le p/2,\qquad E_p(q)<K_p,\qquad E_p(q)=\frac{1-q}{2\left(1-((1+q^p)/2)^{1/p}\right)}.$$

Window I is [21,26], with c=273/625 and q=1011/2500. Window II is [26,32], with c=443/1000 and q=197/500. Two further targets are the unconditional real three-dimensional Hlawka inequalities on these respective windows, as concluded in Section 7 of the source. The previously proved tail for p at least 32 is included as a referenced theorem, preserving its published identity and attribution.

## Significance

The proposed result would extend the known formalized range of the exact diagonal constant from p at least 32 to p at least 21. It would give one constant simultaneously for all complex dimensions and for all real exponents in that range, rather than separate statements at selected integer exponents. The cyclic witnesses also explain the obstruction to decreasing the constant itself.

Formalizing this source means closing the gap between its analytic argument and its finite computations. The [release replay report](https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/results/release-replay.json) records exact rational linear-dual replay and directed interval checks. Those reports support the paper's computer-assisted claim; they are not kernel-checked proofs of the mission's open statements. A completed mission must establish those statements in the platform's ordinary proof system.

## Difficulty

The least constant is defined through a special three-dimensional family, but admissibility quantifies over arbitrary triples in arbitrary dimensions. Unequal singleton norms and degenerate triples are included. Arguments that verify only the cyclic family establish a lower bound and leave the main admissibility assertion unresolved.

The source also requires inequalities uniform in a continuously varying real exponent. Pointwise numerical optimization and dense sampling cannot establish such interval statements. Its localized convexity estimates retain norm bounds and linear coordinate-sum constraints; each retained constraint must genuinely follow from the preceding localization argument, and the averaging domain must remain convex. In particular, retaining a norm-sum equality as if it defined a convex domain would not justify the required averaging step. These issues are part of the formalization target, not additional assumptions supplied to solvers.

## Formalization scope

The environment is Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, using Lean v4.33.1. The goal uses `Fin n → ℂ`, real p, the existing `lpNorm`, `cyclicConstant`, and `HasHlawkaConstant`, and `IsLeast` over real constants. Natural-number dimensions include zero. In dimension zero all coordinate norms vanish, so the inequality is harmless; triples containing zero vectors remain included in positive dimensions. All quantities must retain their foundation definitions.

The four new milestone declarations use the same scalar and coordinate definitions, including the existing `scalarEnvelope`. They introduce no replacement norm and no axiom saying that an external Python execution is correct. The source package contains exact certificates, two arithmetic implementations, and explicit remainder estimates for its rational interval backend. Those implementations share the mathematical model and are not independent end-to-end proofs. Independent analytic review remains pending.

Contributions may reuse the existing dimension reduction, complex transfer, cyclic sharpness, and cutoff-32 results when their hypotheses match the target range. Formalization of the new scalar bounds, exact linear-dual implications, interval arithmetic soundness, and real three-dimensional admissibility is welcome. Proof details and the proposed dependency order are available in the source paper and the milestone descriptions. The declarations uploaded with this proposal are statements to prove, with the standard `by sorry` placeholders; compiling them checks well-formedness only.

## Selected references

- Yuxuan Xu (徐宇轩), School of Computer Science, Wuhan University, *A computer-assisted sharp diagonal Hlawka inequality for real exponents p ≥ 21*, research preprint, v1 (2026). [PDF](https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/paper/main.pdf), [LaTeX](https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/paper/main.tex), [certificates and code](https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/tree/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3). AI assistance is disclosed in the paper.
- K. M. R. Audenaert and F. Kittaneh, *Problems and Conjectures in Matrix and Operator Inequalities*, arXiv:1201.5232v3 (2012), Section 8.2, Problem 7. [Source](https://arxiv.org/abs/1201.5232v3).
- D.-Ş. Marinescu and C. P. Niculescu, *A survey of the Hornich–Hlawka inequality*, arXiv:2407.03278 (2024). [Source](https://arxiv.org/abs/2407.03278).
- Ezzeri Esa / savarin and contributors, *Dimension-independent Hlawka constants for Schatten norms*, Lean source repository (2026). [Repository](https://github.com/savarin/hlawka-schatten).
- Prove2Me contributors, including @bwdaugherty, *Sharp diagonal Hlawka constant: cutoff 32* (2026). [Accepted theorem](https://prove2.me/theorems/6e8430ce-7c32-4b82-9a1b-d7fcd67fdeb3), [campaign](https://prove2.me/campaigns/sharp-diagonal-hlawka-constant). Exact source identifiers and hashes are preserved in the paper repository's [provenance record](https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/sources/provenance.json).
