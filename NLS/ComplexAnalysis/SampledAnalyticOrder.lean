import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! # Analytic order detected on a sequence

An inverse-frequency asymptotic estimate on any nonzero sequence tending
to zero determines the corresponding Taylor jet of an analytic function.
-/
noncomputable section
open Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- A bound along one sequence already forces the analytic vanishing order. -/
theorem analyticOrderAt_ge_of_sampled_bound (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (w : ℕ → ℂ) (hw : Tendsto w atTop (𝓝 0)) (hw0 : ∀ᶠ j in atTop, w j ≠ 0)
    (N : ℕ) (C : ℝ)
    (hb : ∀ᶠ j in atTop, ‖f (w j)‖ ≤ C*‖w j‖^N) :
    (N : ℕ∞) ≤ analyticOrderAt f 0 := by
  by_contra! hlt
  have hfinite : analyticOrderAt f 0 ≠ ⊤ := ne_top_of_lt hlt
  let m := analyticOrderNatAt f 0
  have hm : m < N := by
    have he := Nat.cast_analyticOrderNatAt hfinite
    rw [← he] at hlt
    exact_mod_cast hlt
  obtain ⟨g,hg,hg0,he⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  have hbound : ∀ᶠ j in atTop, ‖g (w j)‖ ≤ C*‖w j‖^(N-m) := by
    filter_upwards [hw.eventually he,hw0,hb] with j hj hj0 hjb
    simp only [sub_zero,smul_eq_mul] at hj
    rw [hj,norm_mul,norm_pow] at hjb
    apply le_of_mul_le_mul_left (a := ‖w j‖^m) ?_ (pow_pos (norm_pos_iff.mpr hj0) m)
    calc
      ‖w j‖^m*‖g (w j)‖ ≤ C*‖w j‖^N := hjb
      _ = ‖w j‖^m*(C*‖w j‖^(N-m)) := by
        rw [← mul_assoc,mul_comm (‖w j‖^m) C,mul_assoc,← pow_add,Nat.add_sub_of_le hm.le]
  have ht : Tendsto (fun j => C*‖w j‖^(N-m)) atTop (𝓝 0) := by
    simpa [Nat.sub_ne_zero_of_lt hm] using (hw.norm.pow (N-m)).const_mul C
  have hz : Tendsto (fun j => ‖g (w j)‖) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound ht
  have hval := tendsto_nhds_unique ((hg.continuousAt.tendsto.comp hw).norm) hz
  exact hg0 (norm_eq_zero.mp hval)

/-- Taylor derivatives below the sampled error order vanish. -/
theorem iteratedDeriv_eq_zero_of_sampled_bound (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (w : ℕ → ℂ) (hw : Tendsto w atTop (𝓝 0)) (hw0 : ∀ᶠ j in atTop, w j ≠ 0)
    (N : ℕ) (C : ℝ)
    (hb : ∀ᶠ j in atTop, ‖f (w j)‖ ≤ C*‖w j‖^N) :
    ∀ k < N, iteratedDeriv k f 0 = 0 :=
  (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp
    (analyticOrderAt_ge_of_sampled_bound f hf w hw hw0 N C hb)

end NLS.ComplexAnalysis
