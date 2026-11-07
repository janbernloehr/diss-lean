import NLS.KdV.HillL2CanonicalActionRatioBound
import NLS.SequenceSpaces.WeightedInfinityAnalyticRealization

/-! The ACTUAL global normalized ACTION amplitude minus one is
analytic in one-order weighted infinity norm near EVERY real L2
source. Both signed coefficients and the unit central mode are retained. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillL2AmplitudeSobolevRemainder (q : Coeff 2) : WeightedCoeff (Weight.sobolev 1) ⊤ :=
  WeightedCoeff.ofFunctionOrZero _ ⊤ (fun k => hillHminusNormalizedAmplitudeSymbol (periodOneL2Inclusion q) k-1)

private theorem root_deviation_le_ratio_deviation (n : ℕ+) (q : PeriodOneHminusOne) :
    ‖hillHminusActionRatioSqrt n q-1‖ ≤ ‖hillHminusCanonicalActionRatio n q-1‖ := by
  have h := norm_sqrt_one_add_sub_one_le (hillHminusCanonicalActionRatio n q-1)
  rw [show 1+(hillHminusCanonicalActionRatio n q-1)=hillHminusCanonicalActionRatio n q by ring] at h
  exact h

private theorem amplitude_weighted_bound (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ+, (1+(n:ℝ))*‖hillHminusCanonicalActionRatio n q-1‖ ≤ C) (k : ℤ) :
    Weight.sobolev 1 k*‖hillHminusNormalizedAmplitudeSymbol q k-1‖ ≤ C := by
  rw [hillHminusNormalizedAmplitudeSymbol_data.1 q hq k]
  by_cases hk : k = 0
  · simp only [hk,Coeff.evenUnitExtension_zero,sub_self,norm_zero,mul_zero]
    exact hC
  · rw [Coeff.evenUnitExtension,dif_neg hk]
    let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr hk⟩
    have h := (mul_le_mul_of_nonneg_left (root_deviation_le_ratio_deviation n q)
      (by positivity : 0 ≤ 1+(n:ℝ))).trans (hb n)
    have hn : (n:ℝ) = |(k:ℝ)| := by
      change (k.natAbs:ℝ) = _
      rw [Nat.cast_natAbs,Int.cast_abs]
    rw [hn] at h
    simpa only [Weight.sobolev_apply,Real.rpow_one] using h

private theorem analytic_amplitude_coordinate (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ hillHminusActionAmplitudeDomain) (k : ℤ) :
    AnalyticAt ℂ (fun r : Coeff 2 => hillHminusNormalizedAmplitudeSymbol (periodOneL2Inclusion r) k-1) q :=
  (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ k).analyticAt _).comp
    (f := fun r : Coeff 2 => hillHminusNormalizedAmplitudeSymbol (periodOneL2Inclusion r))
      ((hillHminusNormalizedAmplitudeSymbol_data.2 _ hq).comp
        (f := fun r : Coeff 2 => periodOneL2Inclusion r) (periodOneL2Inclusion.analyticAt q))).sub analyticAt_const

theorem exists_local_hillL2Amplitude_one_smoothing (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ hillHminusActionAmplitudeDomain) ∧
      ∃ C : ℝ, 0 ≤ C ∧ AnalyticOnNhd ℂ hillL2AmplitudeSobolevRemainder U ∧
        ∀ r ∈ U, ‖hillL2AmplitudeSobolevRemainder r‖ ≤ C ∧ ∀ k : ℤ,
          (hillL2AmplitudeSobolevRemainder r).val k = hillHminusNormalizedAmplitudeSymbol (periodOneL2Inclusion r) k-1 := by
  obtain ⟨U,hU,hqU,hUD,C,hC,hb⟩ := exists_local_hillL2CanonicalActionRatio_weighted_bound q hr
  have h := WeightedCoeff.analytic_infty_realization_of_weighted_bound (Weight.sobolev 1)
    (fun r k => hillHminusNormalizedAmplitudeSymbol (periodOneL2Inclusion r) k-1) hU
    (fun k r hrU => analytic_amplitude_coordinate r (hUD r hrU) k) C hC
    (fun r hrU k => amplitude_weighted_bound _ (hUD r hrU) C hC (hb r hrU) k)
  exact ⟨U,hU,hqU,hUD,C,hC,h.1,h.2⟩

theorem analyticAt_hillL2AmplitudeSobolevRemainder (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    AnalyticAt ℂ hillL2AmplitudeSobolevRemainder q := by
  obtain ⟨U,_,hqU,_,_,_,ha,_⟩ := exists_local_hillL2Amplitude_one_smoothing q hr
  exact ha q hqU

theorem eventually_hillL2AmplitudeSobolevRemainder_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∀ᶠ r in 𝓝 q, ∀ k : ℤ, (hillL2AmplitudeSobolevRemainder r).val k =
      hillHminusNormalizedAmplitudeSymbol (periodOneL2Inclusion r) k-1 := by
  obtain ⟨U,hU,hqU,_,_,_,_,hraw⟩ := exists_local_hillL2Amplitude_one_smoothing q hr
  have hm : ∀ᶠ r in 𝓝 q, r ∈ U := hU.mem_nhds hqU
  exact hm.mono (fun r hrU => (hraw r hrU).2)

theorem hillL2AmplitudeSobolevRemainder_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) (k : ℤ) :
    (hillL2AmplitudeSobolevRemainder q).val k = hillHminusNormalizedAmplitudeSymbol (periodOneL2Inclusion q) k-1 :=
  (eventually_hillL2AmplitudeSobolevRemainder_apply q hr).self_of_nhds k

end NLS.KdV
