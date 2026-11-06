import NLS.KdV.HillL2StateCurve
import NLS.ZakharovShabat.ContinuousSourceBoundaryRealization

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The scalar-state change of variables has polynomial frequency growth. -/
theorem norm_constantUpperStateMap_le (z : ℂ) (v : ℂ × ℂ) :
    ‖constantUpperStateMap z v‖≤(1+‖z‖)*‖v‖ := by
  rw [constantUpperStateMap_apply,Prod.norm_def]
  apply max_le
  · nlinarith [norm_fst_le v,norm_nonneg z,norm_nonneg v]
  · have hh := norm_add_le ((-I*z)*v.1) ((-I)*v.2)
    simp only [norm_mul,norm_neg,norm_I,one_mul] at hh
    nlinarith [norm_fst_le v,norm_snd_le v,norm_nonneg z]

/-- The literal prescribed initial Hill vector has the same frequency growth. -/
theorem norm_constantUpperInitialVector_le (z : ℂ) (v : ℂ × ℂ) :
    ‖constantUpperInitialVector z v‖≤(1+‖z‖)*‖v‖ := by
  rw [constantUpperInitialVector,Prod.norm_def]
  apply max_le
  · nlinarith [norm_fst_le v,norm_nonneg z,norm_nonneg v]
  · have hh := norm_sub_le (I*v.2) (z*v.1)
    simp only [norm_mul,norm_I,one_mul] at hh
    nlinarith [norm_fst_le v,norm_snd_le v,norm_nonneg z]

/-- The actual constant-upper first-order potential has a uniform physical
L2 bound in the original rough scalar source norm. -/
theorem norm_physicalRestrictionL2_hill_le (q : Coeff 2) :
    ‖physicalRestrictionL2 (hillFirstOrderPotential q)‖≤2*(1+‖q‖) := by
  apply (norm_physicalRestrictionL2_le _).trans
  have hh : ‖hillFirstOrderPotential q‖≤1+‖q‖ := by
    simp only [hillFirstOrderPotential,Prod.norm_def,norm_neg,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2),norm_one]
    exact max_le (by nlinarith [norm_nonneg q]) (by linarith)
  exact mul_le_mul_of_nonneg_left hh (by norm_num)

/-- A global growth bound for the genuine rough Hill state in the uniform
physical curve norm, without excluding zero or low frequencies. -/
theorem norm_hillL2FrequencyStateCurve_le (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) :
    ‖hillL2FrequencyStateCurve q z v‖≤
      (1+‖z‖)^2*‖v‖*Real.exp (‖z‖+2*(1+‖q‖)) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  rw [hillL2FrequencyStateCurve_apply]
  apply (norm_constantUpperStateMap_le z _).trans
  have hs := (ContinuousMap.norm_coe_le_norm
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v)) t).trans
    (norm_l2SolutionCurve_le _ _ _)
  have hu := norm_physicalRestrictionL2_hill_le q
  calc
    _ ≤ (1+‖z‖)*(‖constantUpperInitialVector z v‖*
        Real.exp (‖z‖+‖physicalRestrictionL2 (hillFirstOrderPotential q)‖)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (1+‖z‖)*(((1+‖z‖)*‖v‖)*Real.exp (‖z‖+2*(1+‖q‖))) := by
      gcongr
      exact norm_constantUpperInitialVector_le z v
    _ = _ := by ring

end NLS.KdV
