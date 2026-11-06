import NLS.SequenceSpaces.PositiveReindex

/-! Bounded positive-index sampling in the literal l1 norm. The integer
bijection only enumerates positive labels; no coefficient is rescaled. -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS

def positiveOneReindexPull (e : ℤ ≃ ℕ+) (a : Coeff 1) : Coeff 1 :=
  ⟨fun k => a (positiveIndexInjection e k),memℓp_gen
    (((lp.memℓp a).summable (by norm_num : 0<(1 : ℝ≥0∞).toReal)).comp_injective
      (positiveIndexInjection_injective e))⟩

theorem norm_positiveOneReindexPull_le (e : ℤ ≃ ℕ+) (a : Coeff 1) :
    ‖positiveOneReindexPull e a‖≤‖a‖ := by
  have hsum := tsum_comp_le_tsum_of_inj
    ((lp.memℓp a).summable (by norm_num : 0<(1 : ℝ≥0∞).toReal))
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _) (positiveIndexInjection_injective e)
  have hleft := lp.norm_rpow_eq_tsum (by norm_num : 0<(1 : ℝ≥0∞).toReal) (positiveOneReindexPull e a)
  have hright := lp.norm_rpow_eq_tsum (by norm_num : 0<(1 : ℝ≥0∞).toReal) a
  have hs : ‖positiveOneReindexPull e a‖^(1 : ℝ≥0∞).toReal≤‖a‖^(1 : ℝ≥0∞).toReal := by
    rw [hleft,hright]
    exact hsum
  simpa only [ENNReal.toReal_one,Real.rpow_one] using hs

def positiveOneReindexPullCLM (e : ℤ ≃ ℕ+) : Coeff 1 →L[ℂ] Coeff 1 :=
  LinearMap.mkContinuous
    { toFun := positiveOneReindexPull e
      map_add' := by intro a b;ext k;rfl
      map_smul' := by intro c a;ext k;rfl }
    1 (by
      intro a
      change ‖positiveOneReindexPull e a‖≤1*‖a‖
      simpa only [one_mul] using norm_positiveOneReindexPull_le e a)

@[simp] theorem positiveOneReindexPullCLM_apply (e : ℤ ≃ ℕ+) (a : Coeff 1) (k : ℤ) :
    positiveOneReindexPullCLM e a k=a (e k : ℤ) := rfl

end NLS
