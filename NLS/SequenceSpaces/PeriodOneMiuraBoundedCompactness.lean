import NLS.SequenceSpaces.PeriodOneMiuraCompactDerivative
import Mathlib.Topology.Sequences
import NLS.FunctionalAnalysis.CompactPerturbationBoundedPreimages

/-! The actual complex L2 Miura map has compact preimages of compact
Hminus sets after imposing an L2 bound. This uses the compact inclusion of
bounded coefficients into the original Hminus space and the genuine
quadratic convolution, not weak continuity of its coefficients. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS

/-- The rough quadratic product sends L2 bounded sets into relatively
compact sets in the ORIGINAL Hminus norm. -/
theorem isCompact_closure_periodOneMiuraProduct_image (S : Set (Coeff 2))
    (hS : Bornology.IsBounded S) :
    IsCompact (closure ((fun u : Coeff 2 => periodOneMiuraProduct u u) '' S)) := by
  let f : Coeff 2 → Coeff ⊤ := fun u => Coeff.youngConvolution youngRelation_two_two_top u u
  have hb : Bornology.IsBounded (f '' S) := by
    obtain ⟨B,hB⟩ := hS.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B^2,?_⟩
    rintro _ ⟨u,hu,rfl⟩
    have hn := hB u hu
    have hp := norm_nonneg u
    have hB0 : 0 ≤ B := hp.trans hn
    exact (Coeff.norm_youngConvolution_le youngRelation_two_two_top u u).trans
      (by nlinarith)
  have hc := isCompactOperator_boundedCoefficientsHminusOne.isCompact_closure_image_of_bounded hb
  have he : boundedCoefficientsHminusOne '' (f '' S)=
      (fun u : Coeff 2 => periodOneMiuraProduct u u) '' S := by
    rw [Set.image_image]
    rfl
  change IsCompact (closure (boundedCoefficientsHminusOne '' (f '' S))) at hc
  rwa [he] at hc

/-- Compact target sets and bounded sources force strong L2 compactness. -/
theorem isCompact_periodOneMiura_preimage_inter_closedBall
    (K : Set PeriodOneHminusOne) (hK : IsCompact K) (B : ℝ) :
    IsCompact (periodOneMiura ⁻¹' K ∩ closedBall (0 : Coeff 2) B) := by
  have hcont : Continuous periodOneMiura := continuous_iff_continuousAt.mpr (fun u =>
    ((analyticAt_periodOneShiftedMiura 0 u).sub (periodOneL2Inclusion.analyticAt u)).continuousAt)
  apply NLS.FunctionalAnalysis.isCompact_preimage_inter_of_compact_remainders
    periodOneMiura (fun u => periodOneMiuraProduct u u) periodOneL2Inclusion
    (periodOneMassEquiv 0) hcont (fun _ => rfl) _ isClosed_closedBall
    (isCompact_closure_periodOneMiuraProduct_image _ isBounded_closedBall)
    (isCompactOperator_periodOneL2Inclusion.isCompact_closure_image_of_bounded isBounded_closedBall)
    K hK

end NLS
