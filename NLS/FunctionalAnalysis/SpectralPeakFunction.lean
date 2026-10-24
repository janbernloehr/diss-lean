import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Continuous spectral peak functions with uniform pencil bounds -/
noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis

/-- A continuous positive peak equal to one at a, on any complex spectral set. -/
def spectralPeakFunction (s : Set ℂ) (a : ℂ) (ε : ℝ) (hε : 0 < ε) : C(s, ℂ) :=
  ⟨fun x => ((ε/(ε+‖(x : ℂ)-a‖) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (continuous_const.div
      (continuous_const.add (continuous_subtype_val.sub continuous_const).norm)
      (fun _ => ne_of_gt (add_pos_of_pos_of_nonneg hε (norm_nonneg _))))⟩

@[simp] theorem spectralPeakFunction_apply (s : Set ℂ) (a : ℂ) (ε : ℝ)
    (hε : 0 < ε) (x : s) :
    spectralPeakFunction s a ε hε x = ((ε/(ε+‖(x : ℂ)-a‖) : ℝ) : ℂ) := rfl

/-- The peak has its exact value at the distinguished spectral point. -/
theorem spectralPeakFunction_self (s : Set ℂ) (a : s) (ε : ℝ) (hε : 0 < ε) :
    spectralPeakFunction s a ε hε a = 1 := by
  simp [spectralPeakFunction,hε.ne']

/-- The peak is pointwise contractive. -/
theorem norm_spectralPeakFunction_apply_le_one (s : Set ℂ) (a : ℂ)
    (ε : ℝ) (hε : 0 < ε) (x : s) : ‖spectralPeakFunction s a ε hε x‖ ≤ 1 := by
  rw [spectralPeakFunction_apply,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  apply (div_le_one (add_pos_of_pos_of_nonneg hε (norm_nonneg _))).mpr
  exact le_add_of_nonneg_right (norm_nonneg _)

/-- Multiplication by the spectral coordinate minus a is uniformly small. -/
theorem norm_spectralPeakFunction_mul_sub_le (s : Set ℂ) (a : ℂ)
    (ε : ℝ) (hε : 0 < ε) (x : s) :
    ‖spectralPeakFunction s a ε hε x*((x : ℂ)-a)‖ ≤ ε := by
  rw [norm_mul,spectralPeakFunction_apply,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have hd : 0 < ε+‖(x : ℂ)-a‖ := add_pos_of_pos_of_nonneg hε (norm_nonneg _)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  nlinarith [sq_nonneg ε]

/-- The compact-space supremum norm is at most one. -/
theorem norm_spectralPeakFunction_le_one (s : Set ℂ) [CompactSpace s] (a : ℂ)
    (ε : ℝ) (hε : 0 < ε) : ‖spectralPeakFunction s a ε hε‖ ≤ 1 :=
  (ContinuousMap.norm_le _ zero_le_one).mpr (norm_spectralPeakFunction_apply_le_one s a ε hε)

end NLS.FunctionalAnalysis
