import NLS.ComplexAnalysis.CoupledQuadraticIsolation
import NLS.ComplexAnalysis.EntireEvenSquareDescent

/-! The source complex modulus ratio exactly gives the frozen coupling
bounds needed in the two Rouché discs. -/
noncomputable section
namespace NLS.ComplexAnalysis

theorem coupled_sqrt_bounds_of_ratio (b c : ℂ) (hc : c≠0)
    (hl : (1:ℝ)/9≤‖b/c‖) (hh : ‖b/c‖≤9) :
    let u := Complex.sqrt (b*c)
    u≠0 ∧ u^2=b*c ∧ ‖b‖≤3*‖u‖ ∧ ‖c‖≤3*‖u‖ := by
  let u := Complex.sqrt (b*c)
  have hcp : 0<‖c‖ := norm_pos_iff.mpr hc
  rw [norm_div] at hl hh
  have hlow := (le_div_iff₀ hcp).mp hl
  have hhigh := (div_le_iff₀ hcp).mp hh
  have hbp : 0<‖b‖ := by nlinarith
  have hb : b≠0 := norm_pos_iff.mp hbp
  have hsq : u^2=b*c := complex_sqrt_sq (b*c)
  have hup : u≠0 := by
    intro he
    rw [he,zero_pow (by norm_num : 2≠0)] at hsq
    exact mul_ne_zero hb hc hsq.symm
  have hnorm : ‖u‖^2=‖b‖*‖c‖ := by
    simpa only [norm_pow,norm_mul] using congrArg norm hsq
  refine ⟨hup,hsq,?_,?_⟩
  · apply (sq_le_sq₀ (norm_nonneg b) (by positivity : (0:ℝ)≤3*‖u‖)).mp
    have hp := mul_le_mul_of_nonneg_left hhigh (norm_nonneg b)
    nlinarith
  · apply (sq_le_sq₀ (norm_nonneg c) (by positivity : (0:ℝ)≤3*‖u‖)).mp
    have hclow : ‖c‖≤9*‖b‖ := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hclow (norm_nonneg c)
    nlinarith

end NLS.ComplexAnalysis
