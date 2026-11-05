import NLS.KdV.HillNativeActionRatioPositive
import NLS.KdV.HillAbelianCoordinateFactor

/-! # Uniform analytic Abelian amplitudes in the actual half-shift weight -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeAbelianAmplitudePrefactor (k : ℕ+) (u : Coeff 2) : ℂ :=
  sqrt (2*hillNativeActionGapRatio h0q h0r k u)/(Real.sqrt 2 : ℂ)

theorem norm_sq_hillNativeAbelianAmplitudePrefactor (k : ℕ+) (u : Coeff 2) :
    ‖hillNativeAbelianAmplitudePrefactor h0q h0r k u‖^2 = ‖hillNativeActionGapRatio h0q h0r k u‖ := by
  have h := congrArg norm (complex_sqrt_sq (2*hillNativeActionGapRatio h0q h0r k u))
  rw [norm_pow,norm_mul,norm_ofNat] at h
  rw [hillNativeAbelianAmplitudePrefactor,norm_div,div_pow,h,norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem exists_hillNativeAbelianAmplitudePrefactor_all_analytic_bound :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ k : ℕ+,
      AnalyticOnNhd ℂ (hillNativeAbelianAmplitudePrefactor h0q h0r k) (ball (0 : Coeff 2) η) ∧
      ∀ u ∈ ball (0 : Coeff 2) η,
        Real.sqrt (1+(k : ℝ))*‖hillNativeAbelianAmplitudePrefactor h0q h0r k u‖ ≤ C := by
  obtain ⟨η,C,hη,hC,hdata⟩ := exists_hillNativeActionGapRatio_all_positive h0q h0r
  refine ⟨η,Real.sqrt (2*C),hη,Real.sqrt_pos.mpr (by positivity),?_⟩
  intro k
  refine ⟨?_,?_⟩
  · intro u hu
    have hpos : 2*hillNativeActionGapRatio h0q h0r k u ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      left
      have h := (hdata k).2 u hu |>.2
      simp only [mul_re,show (2 : ℂ).re = 2 from rfl,show (2 : ℂ).im = 0 from rfl,zero_mul,sub_zero]
      linarith
    have ha := (Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hpos)).comp
      (f := fun u => 2*hillNativeActionGapRatio h0q h0r k u)
      (analyticAt_const.mul ((hdata k).1 u hu))
    exact ha.div_const
  · intro u hu
    have hbound := ((hdata k).2 u hu).1
    rw [← norm_sq_hillNativeAbelianAmplitudePrefactor h0q h0r] at hbound
    have hk : (0 : ℝ) < k := by positivity
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
    have hb : (k : ℝ)*‖hillNativeAbelianAmplitudePrefactor h0q h0r k u‖^2 ≤ C := by
      have h := (le_div_iff₀ hk).mp hbound
      nlinarith
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg (2*C))).mp
    rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1+(k : ℝ)),
      Real.sq_sqrt (by positivity : 0 ≤ 2*C)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk1) (sq_nonneg ‖hillNativeAbelianAmplitudePrefactor h0q h0r k u‖)]

theorem hillNativeAbelianAmplitudePrefactor_eq_of_ratio (k : ℕ+)
    (q : RealPeriodOneHillPotential) (u : Coeff 2)
    (he : hillNativeActionGapRatio h0q h0r k u = hillActionGapRatio q.val q.property.1 q.property.2 (k : ℕ)) :
    hillNativeAbelianAmplitudePrefactor h0q h0r k u = hillAbelianAmplitudePrefactor q.val q.property.1 q.property.2 (k : ℕ) := by
  have hR := hillActionGapRatio_real_positive q.val q.property.1 q.property.2 (k : ℕ) k.property
  have hr : hillActionGapRatio q.val q.property.1 q.property.2 (k : ℕ) =
      ((hillActionGapRatio q.val q.property.1 q.property.2 (k : ℕ)).re : ℂ) := by
    apply Complex.ext <;> simp only [ofReal_re,ofReal_im,hR.2]
  rw [hillNativeAbelianAmplitudePrefactor,he,hr,← ofReal_ofNat,← ofReal_mul,
    Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR.1.le))]
  rfl

theorem hillNativeAbelianAmplitudePrefactor_zero (k : ℕ+) :
    hillNativeAbelianAmplitudePrefactor h0q h0r k 0 = (Real.sqrt (2*(k : ℝ)*Real.pi) : ℂ)⁻¹ := by
  let q0 : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  have he : hillNativeActionGapRatio h0q h0r k 0 = hillActionGapRatio q0.val q0.property.1 q0.property.2 (k : ℕ) :=
    (hillNativeActionGapRatio_zero h0q h0r k).trans (hillActionGapRatio_free h0q h0r (k : ℕ) k.property).symm
  exact (hillNativeAbelianAmplitudePrefactor_eq_of_ratio h0q h0r k q0 0 he).trans
    (hillAbelianAmplitudePrefactor_free h0q h0r (k : ℕ) k.property)

end NLS.KdV
