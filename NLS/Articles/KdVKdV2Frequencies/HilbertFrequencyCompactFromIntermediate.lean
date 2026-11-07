import NLS.Articles.KdVKdV2Frequencies.IntermediateHilbertPacketAgreement
import NLS.Articles.KdVConvexity.ActionHilbertCompactTransfer

/-! Calibrated intermediate compactness transfers to the ACTUAL Hilbert
Hamiltonian gradient through the SAME original weight and symmetric Hessian. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem physical_hilbert_compact_of_intermediate_packet
    (D : GlobalRoughAbelianForwardData) (E : PhysicalHstarExtension)
    (α : ℝ) (hα0 : -1<α) (hα1 : α< -1/2)
    (U : Set (Coeff 1)) (F : Coeff 1 → Coeff 1)
    (hU : IsOpen U) (hCU : Coeff.nonnegativeLocus 1⊆U) (hF : AnalyticOnNhd ℂ F U)
    (hpair : ∀ (P : NegativeWeightedFrequencyPairChart D (-α) ((α+1)/2)) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → F (quadraticActionsExponent (q := 1) z)=P.packet z)
    (V : Set (Coeff 1)) (G : ℕ+ → Coeff 1 → ℂ)
    (hV : IsOpen V) (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (hcompact : ∀ b∈Coeff.nonnegativeLocus 1,
      IsCompactOperator (fderiv ℂ (fun y => weakActionEnumeration (F y)) b+
        (6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 1)))
    (a : ActionSpace) (ha : a∈positiveQuadrant) :
    IsCompactOperator (fderiv ℂ (actionGradient E.hamiltonian) a+
      (6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace) := by
  exact actionGradient_compact_of_weighted_cone_intertwining E.hamiltonian E.domain E.isOpen E.analytic
    (hilbertIntermediateActionInclusion α hα1) (fun k => Weight.sobolev α (actionIndexEquiv k : ℤ))
    (fun k => (Weight.sobolev α).positive _) (hilbertIntermediateActionInclusion_apply α hα1)
    (hilbertIntermediateActionInclusion_nonnegative α hα1) U
    (fun b => weakActionEnumeration (F b)) hU hCU
    (analyticOnNhd_postcompose_clm weakActionEnumeration F U hF)
    (fun b hbpos => intermediate_packet_hilbert_cone_agreement D E α hα0 hα1 U F hU hCU hF hpair
      V G hV hCV hG hrec b hbpos) hcompact a ha (E.contains_cone ha)

end NLS.Articles.KdVKdV2Frequencies
