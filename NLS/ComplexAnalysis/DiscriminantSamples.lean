import NLS.ComplexAnalysis.ScalarDerivativeInverse
import NLS.ComplexAnalysis.LocalSinhComparison
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Small phases recovered from actual discriminant samples

A fixed analytic inverse of sinh at zero removes the free oscillation
at the half-integer frequency lattice. The construction uses only the
discriminant values. Whenever those samples tend to zero, the recovered
phase tends to zero and gives exactly the original trace eventually.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem exists_smallSinhInverse :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), sinh (g z) = z := by
  have hd : fderiv ℂ sinh 0 = (1 : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
    rw [(hasDerivAt_sinh 0).hasFDerivAt.fderiv]
    apply ContinuousLinearMap.ext
    intro z
    simp
  obtain ⟨g,hg,hg0,_,hr,_⟩ := exists_analytic_localInverse_of_scalar_derivative
    sinh analyticAt_sinh sinh_zero 1 one_ne_zero hd
  exact ⟨g,hg,hg0,hr⟩

def smallSinhInverse : ℂ → ℂ := Classical.choose exists_smallSinhInverse

theorem smallSinhInverse_spec : AnalyticAt ℂ smallSinhInverse 0 ∧ smallSinhInverse 0 = 0 ∧
    ∀ᶠ z in 𝓝 (0 : ℂ), sinh (smallSinhInverse z) = z :=
  Classical.choose_spec exists_smallSinhInverse

def sampleFrequency (j : ℕ) : ℝ := Real.pi*((j : ℝ)+1/2)

theorem sampleFrequency_pos (j : ℕ) : 0 < sampleFrequency j := by
  unfold sampleFrequency
  positivity

theorem sampleFrequency_tendsto : Tendsto sampleFrequency atTop atTop :=
  (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop Real.pi_pos

theorem sampleFrequency_inv_tendsto :
    Tendsto (fun j => (sampleFrequency j : ℂ)⁻¹) atTop (𝓝 0) := by
  simpa only [Function.comp_def,Pi.inv_apply,ofReal_inv,ofReal_zero] using!
    (continuous_ofReal.tendsto 0).comp sampleFrequency_tendsto.inv_tendsto_atTop

theorem cos_sampleFrequency (j : ℕ) : Real.cos (sampleFrequency j) = 0 := by
  have he : sampleFrequency j = (j : ℝ)*Real.pi+Real.pi/2 := by
    unfold sampleFrequency
    ring
  rw [he,Real.cos_add_pi_div_two,Real.sin_nat_mul_pi,neg_zero]

def sampleCarrier (j : ℕ) : ℂ := sinh (-I*(sampleFrequency j : ℂ))

theorem cosh_sampleFrequency (j : ℕ) : cosh (-I*(sampleFrequency j : ℂ)) = 0 := by
  rw [neg_mul,cosh_neg,mul_comm I,cosh_mul_I,← ofReal_cos,cos_sampleFrequency,ofReal_zero]

theorem norm_sampleCarrier (j : ℕ) : ‖sampleCarrier j‖ = 1 := by
  rw [sampleCarrier,neg_mul,sinh_neg,norm_neg,mul_comm I,sinh_mul_I,norm_mul,norm_I,mul_one,
    ← ofReal_sin,norm_real,Real.norm_eq_abs]
  have h := Real.sin_sq_add_cos_sq (sampleFrequency j)
  rw [cos_sampleFrequency] at h
  nlinarith [sq_abs (Real.sin (sampleFrequency j)),abs_nonneg (Real.sin (sampleFrequency j))]

theorem sampleCarrier_ne_zero (j : ℕ) : sampleCarrier j ≠ 0 := by
  intro h
  have hn := norm_sampleCarrier j
  rw [h,norm_zero] at hn
  norm_num at hn

def normalizedTraceSample (T : ℝ → ℂ) (j : ℕ) : ℂ := T (sampleFrequency j)/(2*sampleCarrier j)

def sampledTracePhase (T : ℝ → ℂ) (j : ℕ) : ℂ := smallSinhInverse (normalizedTraceSample T j)

theorem norm_normalizedTraceSample (T : ℝ → ℂ) (j : ℕ) :
    ‖normalizedTraceSample T j‖ = ‖T (sampleFrequency j)‖/2 := by
  simp only [normalizedTraceSample,norm_div,norm_mul,norm_sampleCarrier,mul_one,norm_ofNat]

theorem normalizedTraceSample_tendsto (T : ℝ → ℂ)
    (hT : Tendsto (fun j => T (sampleFrequency j)) atTop (𝓝 0)) :
    Tendsto (normalizedTraceSample T) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_normalizedTraceSample,norm_zero,zero_div] using hT.norm.div_const 2

theorem sampledTracePhase_tendsto (T : ℝ → ℂ)
    (hT : Tendsto (fun j => T (sampleFrequency j)) atTop (𝓝 0)) :
    Tendsto (sampledTracePhase T) atTop (𝓝 0) := by
  simpa only [smallSinhInverse_spec.2.1,Function.comp_def] using!
    smallSinhInverse_spec.1.continuousAt.tendsto.comp (normalizedTraceSample_tendsto T hT)

/-- The small phase is extracted from the original trace and recovers
it exactly for all sufficiently large samples. -/
theorem sampledTracePhase_trace (T : ℝ → ℂ)
    (hT : Tendsto (fun j => T (sampleFrequency j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, 2*cosh (-I*(sampleFrequency j : ℂ)+sampledTracePhase T j) =
      T (sampleFrequency j) := by
  filter_upwards [(normalizedTraceSample_tendsto T hT).eventually smallSinhInverse_spec.2.2] with j hj
  rw [cosh_add,cosh_sampleFrequency,zero_mul,zero_add]
  change 2*(sampleCarrier j*sinh (smallSinhInverse (normalizedTraceSample T j))) = _
  rw [hj,normalizedTraceSample]
  field_simp [sampleCarrier_ne_zero j]

end NLS.ComplexAnalysis
