import NLS.Articles.KdVConvexity.PhysicalFrequencyPairCharts
import NLS.SequenceSpaces.FinitePairActionIdentity

/-! # Actual frequency corrections agree on all real quadratic action fibers -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
open NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVKdV2Frequencies
namespace NLS.Articles.KdVConvexity

theorem originalBaseActionInclusion_injective :
    Function.Injective (fun b : OriginalActionSpace => baseActionInclusion (originalActionInclusion b)) := by
  intro a b h
  apply Subtype.ext
  funext k
  have he := congrArg (fun c : BaseActionSpace => c.val k) h
  simpa only [baseActionInclusion_apply,originalActionInclusion_apply,Equiv.symm_apply_apply] using he

namespace PhysicalFrequencyPairChart

/-- Independently constructed inverse and Miura charts have identical
physical values whenever their real coordinate pairs have equal actions.
Finite physical recovery and simultaneous finite truncation prove this
also at rough sources and at arbitrary infinite-support boundary points. -/
theorem correction_eq_of_real_actions {D : GlobalRoughAbelianForwardData}
    (P Q : PhysicalFrequencyPairChart D)
    (z : Coeff 2 × Coeff 2) (hz : z ∈ P.domain)
    (w : Coeff 2 × Coeff 2) (hw : w ∈ Q.domain)
    (hzr : z ∈ Coeff.realPairLocus 2) (hwr : w ∈ Coeff.realPairLocus 2)
    (ha : quadraticActionsExponent (q := 1) w = quadraticActionsExponent z) (n : ℕ+) :
    P.correction n z=Q.correction n w := by
  apply Coeff.eq_of_finite_pair_action_agreement (q := 1) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    P.domain Q.domain P.domain_open Q.domain_open (P.correction n) (Q.correction n)
    (P.analytic_correction n).continuousOn (Q.analytic_correction n).continuousOn _ z hz w hw hzr hwr ha
  intro S u hu v hv hur hvr huS hvS huv
  obtain ⟨b,hb,hbf⟩ := P.finite_physical_recovery u hu hur S huS
  obtain ⟨c,hc,hcf⟩ := Q.finite_physical_recovery v hv hvr S hvS
  have hact : normalizedCoordinateActions v=normalizedCoordinateActions u :=
    (WeightedCoeff.actionsFromNormalizedCoordinates_eq_iff baseActionWeight v u).mpr huv
  have hbc : b=c := Subtype.ext (originalBaseActionInclusion_injective (hb.trans (hact.symm.trans hc.symm)))
  rw [hbf n,hcf n,hbc]

end PhysicalFrequencyPairChart
end NLS.Articles.KdVConvexity
