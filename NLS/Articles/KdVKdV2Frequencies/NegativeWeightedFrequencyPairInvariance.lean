import NLS.KdV.ClassicalPeriodOperator
import NLS.Articles.KdVKdV2Frequencies.WeightedPairPhysicalRecovery
import NLS.Articles.KdVKdV2Frequencies.NegativeWeightedFrequencyPairCharts
import NLS.Articles.KdVConvexity.PhysicalFrequencyPairInvariance
import NLS.KdV.HillWeightedPairFiniteSupport

/-! Exact physical recovery for finite normalized Sobolev pairs,
followed by simultaneous truncation, proves invariance on every real
action fiber. No finite support or open gap hypothesis remains. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.NegativeWeightedFrequencyPairChart
variable {D : GlobalRoughAbelianForwardData} {β t : ℝ}

theorem finite_physical_recovery (P : NegativeWeightedFrequencyPairChart D β t)
    (z : Coeff 2 × Coeff 2) (hz : z∈P.domain) (hzr : z∈Coeff.realPairLocus 2)
    (S : Finset ℤ) (hS : ∀ k : ℤ, k∉S → z.1 k=0 ∧ z.2 k=0) :
    ∃ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1,
      (∀ k : ℤ, (Weight.sobolev (2*t-1) (actionIndexEquiv k : ℤ) : ℂ)*(baseActionInclusion (originalActionInclusion b.val)).val k=
        quadraticActionsExponent (q := 1) z k) ∧
      ∀ n : ℕ+, P.correction n z=originalPhysicalFrequency b n-(2*(n : ℂ)*Real.pi)^3 := by
  exact finite_weighted_pair_physical_recovery D P.physicalChart t (P.roughPotential z)
    (P.rough_real z hz hzr) (P.rough_zero z hz) (P.rough_mem z hz)
    z hzr (P.rough_signed z hz hzr) S hS

theorem correction_eq_of_real_actions
    (P : NegativeWeightedFrequencyPairChart D β t) (Q : NegativeWeightedFrequencyPairChart D β t)
    (z : Coeff 2 × Coeff 2) (hz : z∈P.domain) (w : Coeff 2 × Coeff 2) (hw : w∈Q.domain)
    (hzr : z∈Coeff.realPairLocus 2) (hwr : w∈Coeff.realPairLocus 2)
    (ha : quadraticActionsExponent (q := 1) w=quadraticActionsExponent z) (n : ℕ+) :
    P.correction n z=Q.correction n w := by
  apply Coeff.eq_of_finite_pair_action_agreement (q := 1) (by norm_num : (2 : ℝ≥0∞)≠⊤)
    P.domain Q.domain P.domain_open Q.domain_open (P.correction n) (Q.correction n)
    (P.analytic_correction n).continuousOn (Q.analytic_correction n).continuousOn _ z hz w hw hzr hwr ha
  intro S u hu v hv hur hvr huS hvS huv
  obtain ⟨b,hb,hbf⟩ := P.finite_physical_recovery u hu hur S huS
  obtain ⟨c,hc,hcf⟩ := Q.finite_physical_recovery v hv hvr S hvS
  have hbc : b=c := by
    apply Subtype.ext
    apply originalBaseActionInclusion_injective
    apply Subtype.ext
    funext k
    apply mul_left_cancel₀ (Weight.complex_ne_zero (Weight.sobolev (2*t-1)) (actionIndexEquiv k : ℤ))
    exact (hb k).trans ((congrArg (fun a : Coeff 1 => a k) huv).symm.trans (hc k).symm)
  rw [hbf n,hcf n,hbc]

theorem packet_eq_of_real_actions (P Q : NegativeWeightedFrequencyPairChart D β t)
    (z : Coeff 2 × Coeff 2) (hz : z∈P.domain) (w : Coeff 2 × Coeff 2) (hw : w∈Q.domain)
    (hzr : z∈Coeff.realPairLocus 2) (hwr : w∈Coeff.realPairLocus 2)
    (ha : quadraticActionsExponent (q := 1) w=quadraticActionsExponent z) : P.packet z=Q.packet w := by
  ext j
  by_cases hj : 0<j
  · let n := positiveIntegerIndex j hj
    have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
    rw [←hnj,P.positive z hz n,Q.positive w hw n]
    exact congrArg (fun v : ℂ => (Weight.sobolev (-β) (n : ℤ) : ℂ)*v)
      (P.correction_eq_of_real_actions Q z hz w hw hzr hwr ha n)
  · rw [P.nonpositive z hz j (by omega),Q.nonpositive w hw j (by omega)]

end NLS.Articles.KdVKdV2Frequencies.NegativeWeightedFrequencyPairChart
