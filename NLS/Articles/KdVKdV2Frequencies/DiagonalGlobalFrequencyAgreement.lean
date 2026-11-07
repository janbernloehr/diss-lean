import NLS.Articles.KdVKdV2Frequencies.DiagonalFrequencyPairCharts
import NLS.Articles.KdVKdV2Frequencies.NegativeWeightedFrequencyPairInvariance

/-! The actual diagonal chart's FULL correction agrees with the
already global intermediate frequency, across independently chosen
physical charts, by original finite physical calibration and continuity. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem NegativeWeightedFrequencyPairChart.correction_eq_of_diagonal_pair
    {D : GlobalRoughAbelianForwardData} {I : PeriodOneHminusOne → BaseActionSpace} {β t : ℝ}
    (P : NegativeWeightedFrequencyPairChart D β t) (Q : DiagonalFrequencyPairChart D I t)
    (z : Coeff 2 × Coeff 2) (hz : z∈P.domain) (w : Coeff 2 × Coeff 2) (hw : w∈Q.domain)
    (hzr : z∈Coeff.realPairLocus 2) (hwr : w∈Coeff.realPairLocus 2)
    (ha : quadraticActionsExponent (q := 1) w=quadraticActionsExponent z) (n : ℕ+) :
    P.correction n z=Q.physicalChart.correction n (Q.roughPotential w) := by
  have hQa : AnalyticOnNhd ℂ (fun v => Q.physicalChart.correction n (Q.roughPotential v)) Q.domain :=
    fun v hv => (Q.physicalChart.analytic_correction n _ (Q.rough_mem v hv)).comp (Q.analytic_potential v hv)
  apply Coeff.eq_of_finite_pair_action_agreement (q := 1) (by norm_num : (2 : ℝ≥0∞)≠⊤)
    P.domain Q.domain P.domain_open Q.domain_open (P.correction n)
    (fun v => Q.physicalChart.correction n (Q.roughPotential v))
    (P.analytic_correction n).continuousOn hQa.continuousOn _ z hz w hw hzr hwr ha
  intro S u hu v hv hur hvr huS hvS huv
  obtain ⟨b,hb,hbf⟩ := P.finite_physical_recovery u hu hur S huS
  obtain ⟨c,hc,hcf⟩ := finite_weighted_pair_physical_recovery D Q.physicalChart t
    (Q.roughPotential v) (Q.rough_real v hv hvr) (Q.rough_zero v hv) (Q.rough_mem v hv)
    v hvr (Q.rough_signed v hv hvr) S hvS
  have hbc : b=c := by
    apply Subtype.ext
    apply originalBaseActionInclusion_injective
    apply Subtype.ext
    funext k
    apply mul_left_cancel₀ (Weight.complex_ne_zero (Weight.sobolev (2*t-1)) (actionIndexEquiv k : ℤ))
    exact (hb k).trans ((congrArg (fun a : Coeff 1 => a k) huv).symm.trans (hc k).symm)
  rw [hbf n,hcf n,hbc]

theorem global_negativeWeighted_packet_diagonal_recovery
    (D : GlobalRoughAbelianForwardData) (β t : ℝ)
    (hβ : 0<β) (hβ1 : β<1) (ht : 0<t) (hβt : 2*t=1-β)
    (F : Coeff 1 → Coeff 1)
    (hpair : ∀ (P : NegativeWeightedFrequencyPairChart D β t) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → F (quadraticActionsExponent (q := 1) z)=P.packet z)
    {I : PeriodOneHminusOne → BaseActionSpace} (Q : DiagonalFrequencyPairChart D I t)
    (z : Coeff 2 × Coeff 2) (hz : z∈Q.domain) (hzr : z∈Coeff.realPairLocus 2) (n : ℕ+) :
    F (quadraticActionsExponent (q := 1) z) (n : ℤ)=
      (Weight.sobolev (-β) (n : ℤ) : ℂ)*Q.physicalChart.correction n (Q.roughPotential z) := by
  obtain ⟨P,hzP⟩ := exists_negativeWeightedFrequencyPairChart D β t hβ hβ1 ht hβt z hzr
  rw [hpair P z hzP hzr,P.positive z hzP n]
  exact congrArg (fun a : ℂ => (Weight.sobolev (-β) (n : ℤ) : ℂ)*a)
    (P.correction_eq_of_diagonal_pair Q z hzP z hz hzr hzr rfl n)

end NLS.Articles.KdVKdV2Frequencies
