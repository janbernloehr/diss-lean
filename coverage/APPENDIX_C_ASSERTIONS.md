# Appendix C ordered assertion comparison

The ordered Appendix C comparison covers nine groups on printed pp.125–126: six matched, two directly corrected and one contextual, with no partial or pending groups in this local comparison. C.1 uses the corrected boundedness statement for every finite 1<p<infinity, with actual absolutely convergent omitted-diagonal rows. C.2 retains arbitrary bounded complex displacements, the exact separation, the pi normalization and a uniform operator bound. The two correction operators have their literal rows and A=H+F-G, directly correcting the swapped source labels. Separate norm and finite-p power estimates retain c and c^p explicitly. Only the corrections include both Banach endpoints. This documentation step adds no Lean proof or refutation. Historical corrections, refutations and broader completeness qualifications remain unchanged.

Source: printed pp.125–126, text lines 10247–10315. Line numbers count
newline characters and preserve form feeds. Both rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| C-001 | 10249–10250 | Context and classical discrete Hilbert transform | contextual |
| C-002 | 10252–10260 | C.1 corrected bounded transform statement | corrected |
| C-003 | 10263–10264 | Unperturbed lattice normalization | matched |
| C-004 | 10275–10278 | C.2 displacement and separation assumptions | matched |
| C-005 | 10280–10287 | Actual modified transform and uniform bound | matched |
| C-006 | 10290–10294 | Reciprocal kernel identity | matched |
| C-007 | 10296–10302 | Separate F/G operators with corrected labels | corrected |
| C-008 | 10305–10311 | Pointwise and powered norm estimates with explicit separation constant | matched |
| C-009 | 10313–10314 | Young convolution estimate and analogous G estimate | matched |

## Compared passages

### C-001: Context and classical discrete Hilbert transform

- The appendix recalls the discrete Hilbert transform on complex sequence spaces and then treats two perturbed lattices.

Public declarations:

- `NLS.Fourier.sourceLemmaC1_bounded`
- `NLS.Fourier.sourceLemmaC2`

The literature attribution is contextual; the public implementation supplies the actual operators and convergent series.

### C-002: C.1 corrected bounded transform statement

- For every finite 1<p<infinity, there is a unique bounded complex linear operator whose output is the genuinely convergent omitted-diagonal series sum x_m/(m-n).
- The signed denominator, all infinite-support inputs and absolute convergence are retained.

Public declarations:

- `NLS.Fourier.sourceHilbert_hasSum`
- `NLS.Fourier.sourceLemmaC1_bounded`
- `NLS.Fourier.summable_norm_hilbertSeries_of_finite`

Use the corrected boundedness statement. The existing review records the historical correction to the printed isomorphism assertion; that evidence is preserved unchanged. This comparison adds no refutation and does not repeat or extend the obstruction proof.

### C-003: Unperturbed lattice normalization

- The reference lattice is sigma0_n=pi*n; the modified transform includes the outer factor pi.
- A common constant complex displacement in both lattices gives precisely the ordinary transform.

Public declarations:

- `NLS.Fourier.hilbertLattice`
- `NLS.Fourier.modifiedHilbert_common_constant`

The common displacement cancels in every off-diagonal denominator. The omitted diagonal stays omitted even when the two displaced lattices differ there.

### C-004: C.2 displacement and separation assumptions

- Both displacement sequences may be arbitrary bounded complex sequences.
- For c>0, the exact hypothesis is c^(-1)*norm(m-n)<=norm(rho_m-sigma_n) for every m!=n.

Public declarations:

- `NLS.Fourier.HilbertLatticeSeparated`
- `NLS.Fourier.sourceLemmaC2`

No smallness, reality, ordering or finite-support assumption is introduced. The separation is required only off the diagonal.

### C-005: Actual modified transform and uniform bound

- For each finite 1<p<infinity, the actual series pi*sum_{m!=n} x_m/(rho_m-sigma_n) defines a unique bounded complex linear operator.
- One bound is chosen before the two lattices from p,c and displacement norm bounds S,R; it is C_p+c*(S+R)*norm(square kernel).

Public declarations:

- `NLS.Fourier.sourceModifiedHilbert_hasSum`
- `NLS.Fourier.sourceLemmaC2`
- `NLS.Fourier.norm_modifiedHilbert_le`
- `NLS.Fourier.exists_modifiedHilbert_uniform_bound`

The quantifier order is uniform over every separated pair with these norm bounds. The full transform is asserted only for finite 1<p<infinity; the correction operators separately extend to both Banach endpoints.

### C-006: Reciprocal kernel identity

- Subtracting the ordinary kernel gives exactly (s_n-r_m)/((m-n)*(rho_m-sigma_n)).
- The separate two-denominator kernel is bounded by c times the summable reciprocal-square kernel, and the joint correction bound uses c*(norm(s)+norm(r)).

Public declarations:

- `NLS.Fourier.modifiedHilbertKernel_sub`
- `NLS.Fourier.norm_modifiedHilbertKernel_sub_le`
- `NLS.Fourier.norm_modifiedHilbertSecondKernel_le`

The zero diagonal and signed difference are accounted for before forming the absolutely convergent row sums. The new separate-kernel bound passed its full check and is committed and pushed.

### C-007: Separate F/G operators with corrected labels

- F uses the output displacement s_n and G uses the input displacement r_m in the two exact source series.
- The resulting bounded operators satisfy correction=F-G and A=H+F-G.

Public declarations:

- `NLS.Fourier.modifiedHilbertF`
- `NLS.Fourier.modifiedHilbertG`
- `NLS.Fourier.modifiedHilbertF_hasSum`
- `NLS.Fourier.modifiedHilbertG_hasSum`
- `NLS.Fourier.modifiedHilbertCorrection_eq_F_sub_G`
- `NLS.Fourier.modifiedHilbert_eq_H_add_F_sub_G`

Correct the swapped labels in the displayed decomposition directly. Both operators depend on both lattices; the labels specify which displacement appears in the numerator. These positive theorems passed their full check and are committed and pushed.

### C-008: Pointwise and powered norm estimates with explicit separation constant

- The pointwise F bound is c*norm(s)*the positive square-kernel convolution of abs(x).
- At every finite Banach exponent, the powered sum is bounded by c^p*norm(s)^p times the powered majorant sum.
- The final F estimate retains c^p*norm(s)^p*norm(square kernel)^p*norm(x)^p explicitly.

Public declarations:

- `NLS.Fourier.norm_modifiedHilbertF_apply_le`
- `NLS.Fourier.tsum_norm_modifiedHilbertF_rpow_le_majorant`
- `NLS.Fourier.tsum_norm_modifiedHilbertF_rpow_le`

The source already displays c^p in the first estimate. Keep it explicit in the final estimate as well instead of hiding its dependence in C_p. All powered sums converge; these positive theorems passed their full check and are committed and pushed.

### C-009: Young convolution estimate and analogous G estimate

- Young convolution with the summable reciprocal-square kernel bounds the majorant on every Banach coefficient space.
- F and G individually have norm bounds c*norm(s or r)*norm(square kernel)*norm(x), including p=1 and infinity; the finite-p G power estimate is explicit.

Public declarations:

- `NLS.Fourier.norm_hilbertSquareMajorant_le`
- `NLS.Fourier.norm_modifiedHilbertF_le`
- `NLS.Fourier.norm_modifiedHilbertG_le`
- `NLS.Fourier.tsum_norm_modifiedHilbertG_rpow_le`

The finite-p powered G sum uses the input displacement norm. Adding the ordinary transform gives the original finite 1<p<infinity C.2 scope. These positive theorems passed their full check and are committed and pushed.

## Evidence and validation

The [source transform statements](../NLS/Fourier/AppendixCSourceTransform.lean)
retain actual convergent omitted-diagonal series and the uniform lattice bound.
The [separate corrections](../NLS/Fourier/ModifiedHilbertSeparateCorrections.lean)
supply F and G with the corrected labels and explicit separation constants.

This comparison read ten complete public module bodies and resolves
26 declarations. It reconciles the previous Appendix C review and the
new positive operator construction. Historical refutations remain unchanged;
no obstruction proof is repeated or extended. This is a local source
comparison, not a fresh review of every transitive Hilbert-transform proof.

The unchanged Lean snapshot reuses the successful full check recorded at commit 84c1afb63ef673079ec78066d2e9fc55c2ce1e1a: 8,584 build jobs, 7,697 public examples and an axiom audit of 44,742 NLS declarations, with 21 inherited warnings and zero new. All 26 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: Appendix D. The
[broader completion qualifications](COMPLETENESS.md) remain.
