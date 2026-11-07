import NLS.Articles.KdVKdV2Frequencies.HilbertIntermediateActionInclusion
import NLS.Articles.KdVKdV2Frequencies.GlobalScalarHilbertFrequencyAgreement
import NLS.Articles.KdVKdV2Frequencies.NegativeWeightedWeakFrequencyCompatibility
import NLS.Articles.KdVConvexity.ActionHilbertGradientCoordinates

/-! The ACTUAL intermediate global packet intertwines with the ACTUAL
physical Hilbert gradient on the ENTIRE nonnegative Hilbert cone. The
source and target use the SAME original positive-label weight. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem intermediate_packet_hilbert_cone_agreement
    (D : GlobalRoughAbelianForwardData) (E : PhysicalHstarExtension)
    (α : ℝ) (hα : -1<α) (hα1 : α< -1/2)
    (U : Set (Coeff 1)) (F : Coeff 1 → Coeff 1)
    (hU : IsOpen U) (hCU : Coeff.nonnegativeLocus 1⊆U) (hF : AnalyticOnNhd ℂ F U)
    (hpair : ∀ (P : NegativeWeightedFrequencyPairChart D (-α) ((α+1)/2)) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → F (quadraticActionsExponent (q := 1) z)=P.packet z)
    (V : Set (Coeff 1)) (G : ℕ+ → Coeff 1 → ℂ)
    (hV : IsOpen V) (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a : Coeff 2) (ha : a∈Coeff.nonnegativeLocus 2) :
    weakActionEnumeration (F (hilbertIntermediateActionInclusion α hα1 a))=
      hilbertIntermediateActionInclusion α hα1 (normalizedActionGradient E.hamiltonian a) := by
  have hapos : actionUnreindex a∈positiveQuadrant := by
    intro n
    exact ha (actionIndexEquiv.symm n)
  ext i
  have hfreq := negativeWeighted_packet_agrees_actual_weak_frequency D (-α) ((α+1)/2)
    (by linarith) (by linarith) (by linarith) (by ring) U F hU hCU hF hpair V G hV hCV hG hrec
      (hilbertIntermediateActionInclusion α hα1 a) (hilbertIntermediateActionInclusion_nonnegative α hα1 a ha)
        (actionIndexEquiv i)
  simp only [neg_neg] at hfreq
  rw [weakActionEnumeration_apply,hilbertIntermediateActionInclusion_apply,hfreq,
    hilbertIntermediateActionInclusion_weak]
  rw [global_scalar_frequency_eq_physical_hilbert_gradient D E V G hV hCV hG
    (global_physical_family_native_recovery D G hrec) (actionUnreindex a) hapos]
  rfl

end NLS.Articles.KdVKdV2Frequencies
