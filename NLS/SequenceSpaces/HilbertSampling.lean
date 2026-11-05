import NLS.SequenceSpaces.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Contractive injective sampling of Hilbert coefficient sequences -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Coeff

def hilbertSample (e : ℤ ↪ ℤ) (a : Coeff 2) : Coeff 2 :=
  ⟨fun k => a (e k),by
    apply memℓp_gen
    exact ((lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).comp_injective e.injective⟩

@[simp] theorem hilbertSample_apply (e : ℤ ↪ ℤ) (a : Coeff 2) (k : ℤ) :
    hilbertSample e a k = a (e k) := rfl

theorem norm_hilbertSample_le (e : ℤ ↪ ℤ) (a : Coeff 2) : ‖hilbertSample e a‖ ≤ ‖a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hs : Summable (fun k : ℤ => ‖a k‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have heq (b : Coeff 2) : ‖b‖^2 = ∑' k : ℤ, ‖b k‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) b
  rw [heq,heq]
  simp only [hilbertSample_apply]
  exact tsum_comp_le_tsum_of_inj hs (fun _ => sq_nonneg _) e.injective

def hilbertSampleCLM (e : ℤ ↪ ℤ) : Coeff 2 →L[ℂ] Coeff 2 :=
  LinearMap.mkContinuous
    { toFun := hilbertSample e
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    1 (by intro a; simpa only [one_mul] using! norm_hilbertSample_le e a)

@[simp] theorem hilbertSampleCLM_apply (e : ℤ ↪ ℤ) (a : Coeff 2) (k : ℤ) :
    hilbertSampleCLM e a k = a (e k) := rfl

end NLS.Coeff
