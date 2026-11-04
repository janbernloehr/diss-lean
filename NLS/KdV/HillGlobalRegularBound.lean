import NLS.KdV.HillGlobalRegularCorrection

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillRegularAbelianPrimitive_real_eq_mean_free_integral
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (θ : ℝ) :
    hillRegularAbelianPrimitive q hq hr n hn k (θ:ℂ) =
      ∫ t in Real.pi..θ, hillAbelianCosineDifferential q hq hr n hn k (t:ℂ)-(if k=n then 1 else 0) := by
  have hint : IntervalIntegrable (fun t : ℝ => hillAbelianCosineDifferential q hq hr n hn k (t:ℂ)) volume Real.pi θ :=
    (continuous_hillAbelianCosineDifferential_real q hq hr n hn k hk).intervalIntegrable Real.pi θ
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const,intervalIntegral.integral_const]
  unfold hillRegularAbelianPrimitive
  rw [hillAbelianCosinePrimitive_real_eq_intervalIntegral]
  simp only [Complex.real_smul,ofReal_sub]
  ring

theorem norm_hillRegularAbelianCorrection_le_of_differential_bound
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ E ∈ segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ),
      ‖-I*hillAbelianSelectedGlobalPsi q hq hr n hn E/hillDeflatedEnergyCanonicalRoot q hq hr k E-
        (if k=n then 1 else 0)‖ ≤ B) :
    ‖hillRegularAbelianCorrection q hq hr n hn k hk‖ ≤ 2*Real.pi*B := by
  by_cases hc : hillRealGapHalfLength q hq hr k = 0
  · rw [hillRegularAbelianCorrection_closed q hq hr n hn k hk hc,norm_zero]
    positivity
  let θ := hillDirichletSelectedRealAngle q hq hr k hk hc
  have hθ : θ ∈ Icc (-Real.pi) Real.pi := (hillDirichletSelectedRealAngle_spec q hq hr k hk hc).1
  rw [hillRegularAbelianCorrection,dif_neg hc,hillRegularAbelianPrimitive_real_eq_mean_free_integral q hq hr n k hn hk θ]
  have hb (t : ℝ) (_ht : t ∈ Set.uIoc Real.pi θ) :
      ‖hillAbelianCosineDifferential q hq hr n hn k (t:ℂ)-(if k=n then 1 else 0)‖ ≤ B := by
    simpa only [hillAbelianCosineDifferential,mul_div_assoc] using
      hbound _ (hillCosineGapPoint_mem_real_gap q hq hr k hk t)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hdist : |θ-Real.pi| ≤ 2*Real.pi := by
    rw [abs_of_nonpos (sub_nonpos.mpr hθ.2)]
    linarith [hθ.1]
  exact h.trans ((mul_le_mul_of_nonneg_left hdist hB).trans_eq (by ring))

end NLS.KdV
