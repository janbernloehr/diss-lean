# mKdV below L² — main-theorem verification

**Theorems 1.1, 1.2 and 1.3 are verified under the accepted intrinsic
Birkhoff reference and the normalization qualifications recorded below.**

The work is on the private `articles/mkdv-below-l2` branch, based on canonical
commit `c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. The canonical checkout and
its compiled dependencies are unchanged. The workspace decision remains separate.

## Source and clause maps

Kappeler–Molnar, *On the wellposedness of the defocusing mKdV equation below L²*,
[arXiv:1606.07052v1](https://arxiv.org/abs/1606.07052v1).
The served 33-page PDF was downloaded on 2026-11-02 and has SHA-256
`7ac1baa898365f4a556aec4d2e3182e82a9dbe782d8a183114ae81acb486e8c1`.
It displays November 14, 2021 although the requested version and watermark
are v1, 22 June 2016. The hash pins the actual served bytes.

| Source theorem | Lean declarations | Clause map |
| --- | --- | --- |
| 1.1, p. 3 | `theorem1_1` | [Theorem 1.1](theorem-1.1.json) |
| 1.2, p. 5 | `theorem1_2_at_exponent`, `theorem1_2_compatible`, Hilbert clauses | [Theorem 1.2](theorem-1.2.json) |
| 1.3, p. 6 | `theorem1_3_hilbert`, `theorem1_3_extension`, `theorem1_3_asymptotic` | [Theorem 1.3](theorem-1.3.json) |

All declarations are in namespace `NLS.Articles.MKdVBelowL2`.

## Theorem 1.1

For every finite p>2, renormalized physical mKdV is locally C⁰-wellposed at
every original real scalar Fourier–Lebesgue datum and globally C⁰-wellposed
on one invariant open neighborhood of zero chosen before all T>0. Dependence
on initial data is continuous in the full uniform trajectory norm.
The solution definition quantifies over every smooth real initial-data
sequence converging in the original physical Fourier norm. Genuine smooth
sequences exist at every datum, and all such approximants converge uniformly
on the common compact time interval. Classical physical PDE uniqueness
identifies the smooth solution map, so it is not an assumed flow label.

The original ordinary mKdV smooth solution map has no continuous extension
at any original real datum outside physical L², for each selected t>0.
This also holds for relative continuity on smooth data plus one rough point,
and even when smooth agreement is required only near the point.
The L² locus is identified with actual period-one L² functions representing
the same original distribution. A mass-restored Hilbert phase family solves
the ordinary physical PDE and has the exact fixed Birkhoff coordinate law.
Controlled smooth real approximants converge in the original scalar norm
while giving exactly opposite mass phases at that same selected time.

## Theorems 1.2 and 1.3

Theorem 1.2 uses one compatible family on original period-one distributions.
It has the stated complex analytic domains, canonical physical brackets,
zero normalization, injective real analytic local inverses, and open dense
real image in the actual conjugate-pair target. At p=2 it agrees with the
accepted intrinsic Hilbert map and has a global real analytic inverse.

Theorem 1.3 gives real analyticity of the normalized physical H₄ frequencies
into every stated Hilbert weighted target and the literal ell^(-1,p/2)
target for finite p>2. The frequencies equal the independent full native
H^(3/2) Hamiltonian action derivatives, including closed actions. One
neighborhood and both remainder maps precede every finite q>1 in the locally
uniform asymptotic; the p/3 quasi-norm is retained when 2<p<3.

## Qualifications and corrections

The accepted Grébert–Kappeler manuscript reference used for the intrinsic
Hilbert Birkhoff map is retained; PDF edition identity is outside the agreed
scope. Real and complex norm models are connected by explicit continuous
linear equivalences. This reference qualification adds no axiom.

The physical first Hamiltonian phase has the negative sign. The ordinary
frequency restores 12*pi*n times the actual physical mass; both the ordinary
and renormalized displayed PDEs are proved directly. This avoids an apparent
spatial translation sign inconsistency in the source prose. The proof of
Corollary 7.2(iii) cites a nonexistent item (iv) of Theorem 7.1; the formal
proof supplies the required fixed-time argument and physical calibration.

The printed n-times-remainder expression is an asymptotic at infinity. Its
Lean asymptotic clause uses n!=0; the exact all-index formula separately
retains the actual singleton contribution at n=0. No general complex
zero-frequency vanishing or Banach assumption at p/3<1 is inserted.

## Validation and scope

The focused checker lists 219 shared/article modules. The final checkpoint
strictly checks 15 new modules with Lean 4.33.1, `autoImplicit=false` and
`warningAsError=true`, and reuses 204 unchanged modules after byte comparison
with `ef4b1eb1c007ed660156037a999289daa3ae7948`.
A fresh full transitive audit checks 1007 named declarations, including all
main theorems. Only `propext`, `Classical.choice` and `Quot.sound` occur.
No holes, new axioms, disabled linters or increased heartbeat/recursion limits
were introduced. Canonical compiled dependencies are imported read-only.
This is incremental focused validation, not a fresh whole-repository rebuild.

See [validation evidence](validation.json), [compiler and audit output](validation.txt),
[completion audit](completion-audit.json), and [checkpoint history](PROGRESS.md).
The goal covers these main theorems and their necessary dependencies, rather
than every remark or ancillary statement in the article.
