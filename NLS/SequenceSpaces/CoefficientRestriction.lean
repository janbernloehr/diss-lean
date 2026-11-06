import NLS.SequenceSpaces.WeightedInsertion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.Coeff

variable {p : ℝ≥0∞} [Fact (1≤p)]

/-- Restrict coefficients along an injective integer index map. -/
def restrictIndices (e : ℤ ↪ ℤ) (a : Coeff p) : Coeff p :=
  ⟨fun n => a (e n),by
    change Memℓp (fun n => a (e n)) p
    by_cases hp : p=⊤
    · subst p
      apply memℓp_infty
      refine ⟨‖a‖,?_⟩
      rintro _ ⟨n,rfl⟩
      exact lp.norm_apply_le_norm (by simp) a (e n)
    · have hp0 : 0<p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1≤p)).ne' hp
      rw [memℓp_gen_iff hp0]
      exact ((lp.memℓp a).summable hp0).comp_injective e.injective⟩

theorem norm_restrictIndices_le (e : ℤ ↪ ℤ) (a : Coeff p) : ‖restrictIndices e a‖≤‖a‖ := by
  by_cases hp : p=⊤
  · subst p
    exact lp.norm_le_of_forall_le (norm_nonneg a) (fun n => lp.norm_apply_le_norm (by simp) a (e n))
  · have hp0 : 0<p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1≤p)).ne' hp
    rw [lp.norm_eq_tsum_rpow hp0,lp.norm_eq_tsum_rpow hp0]
    apply Real.rpow_le_rpow (tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
    · exact tsum_comp_le_tsum_of_inj ((lp.memℓp a).summable hp0)
        (fun _ => Real.rpow_nonneg (norm_nonneg _) _) e.injective
    · positivity

def restrictIndicesCLM (e : ℤ ↪ ℤ) : Coeff p →L[ℂ] Coeff p :=
  LinearMap.mkContinuous
    { toFun := restrictIndices e
      map_add' := by intro a b;ext n;rfl
      map_smul' := by intro c a;ext n;rfl } 1 (by
    intro a
    change ‖restrictIndices e a‖≤1*‖a‖
    simpa only [one_mul] using norm_restrictIndices_le e a)

end NLS.Coeff
