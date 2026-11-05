import NLS.KdV.HillHminusUniformPhysicalActionRatios

/-! # Uniform physical Abelian amplitudes on the rough infinite tail -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillHminusActionRatioAmplitude (R : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) : ℂ :=
  sqrt (2*R q)/(Real.sqrt 2 : ℂ)

theorem norm_sq_hillHminusActionRatioAmplitude (R : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) :
    ‖hillHminusActionRatioAmplitude R q‖^2=‖R q‖ := by
  have h := congrArg norm (complex_sqrt_sq (2*R q))
  rw [norm_pow,norm_mul,norm_ofNat] at h
  rw [hillHminusActionRatioAmplitude,norm_div,div_pow,h,norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

include h0q h0r in
theorem exists_hillHminus_high_physical_action_amplitudes :
    ∃ η : ℝ, ∃ N : ℕ, 0 < η ∧ 2 ≤ N ∧ ∀ n : ℕ+, N ≤ (n : ℕ) →
      ∃ B : PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ B (ball (0 : PeriodOneHminusOne) η) ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) η, Real.sqrt (1+(n : ℝ))*‖B q‖ ≤ 2) ∧
        ∀ p : RealPeriodOneHillPotential,
          (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η →
          B (hillPhysicalHminusEmbedding p).val =
            hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  obtain ⟨η,N,hη,hN,hfamily⟩ := exists_hillHminus_high_physical_action_ratios h0q h0r
  refine ⟨η,N,hη,hN,?_⟩
  intro n hn
  obtain ⟨R,hRa,hRb,hRp⟩ := hfamily n hn
  refine ⟨hillHminusActionRatioAmplitude R,?_,?_,?_⟩
  · intro q hq
    have hslit : 2*R q ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      left
      simp only [mul_re,show (2 : ℂ).re=2 from rfl,show (2 : ℂ).im=0 from rfl,zero_mul,sub_zero]
      linarith [(hRb q hq).2]
    exact ((Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hslit)).comp
      (f := fun q => 2*R q) (analyticAt_const.mul (hRa q hq))).div_const
  · intro q hq
    have hbound := (hRb q hq).1
    rw [← norm_sq_hillHminusActionRatioAmplitude] at hbound
    have hnpos : (0 : ℝ) < n := by positivity
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.property
    have hb : (n : ℝ)*‖hillHminusActionRatioAmplitude R q‖^2 ≤ 2 := by
      have h := (le_div_iff₀ hnpos).mp hbound
      nlinarith
    apply (sq_le_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 2)).mp
    rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1+(n : ℝ))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg ‖hillHminusActionRatioAmplitude R q‖)]
  · intro p hp
    have hratio := hRp p hp
    have hreal := hillActionGapRatio_real_positive p.val p.property.1 p.property.2 (n : ℕ) n.property
    have hcast : hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ)=
        ((hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ)).re : ℂ) := by
      apply Complex.ext <;> simp only [ofReal_re,ofReal_im,hreal.2]
    rw [hillHminusActionRatioAmplitude,hratio,hcast,← ofReal_ofNat,← ofReal_mul,
      Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hreal.1.le))]
    rfl

end NLS.KdV
