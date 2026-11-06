import NLS.SequenceSpaces.LocallyBoundedRealization
import Mathlib.Logic.Equiv.Nat

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.Coeff



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def natL1OfFunction (f : ℕ → ℂ) : Coeff 1 :=
  ofFunctionOrZero 1 (fun j : ℤ => f (Equiv.intEquivNat j))

theorem natL1OfFunction_apply_of_summable (f : ℕ → ℂ)
    (hf : Summable (fun n => ‖f n‖)) (n : ℕ) :
    natL1OfFunction f (Equiv.intEquivNat.symm n)=f n := by
  have hs : Summable (fun j : ℤ => ‖f (Equiv.intEquivNat j)‖) := Equiv.intEquivNat.summable_iff.mpr hf
  have hm : Memℓp (fun j : ℤ => f (Equiv.intEquivNat j)) 1 := by
    rw [memℓp_gen_iff (by norm_num : 0<(1:ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_one,Real.rpow_one] using hs
  rw [natL1OfFunction,ofFunctionOrZero_apply_of_mem 1 _ hm,Equiv.apply_symm_apply]

theorem norm_natL1OfFunction_eq_tsum (f : ℕ → ℂ)
    (hf : Summable (fun n => ‖f n‖)) :
    ‖natL1OfFunction f‖=∑' n : ℕ, ‖f n‖ := by
  have hn (j : ℤ) : natL1OfFunction f j=f (Equiv.intEquivNat j) := by
    have hh := natL1OfFunction_apply_of_summable f hf (Equiv.intEquivNat j)
    simpa only [Equiv.symm_apply_apply] using hh
  have he := lp.norm_rpow_eq_tsum (by norm_num : 0<(1:ℝ≥0∞).toReal) (natL1OfFunction f)
  calc
    _ = ∑' j : ℤ, ‖f (Equiv.intEquivNat j)‖ := by simpa only [ENNReal.toReal_one,Real.rpow_one,hn] using he
    _ = _ := Equiv.intEquivNat.tsum_eq (fun n : ℕ => ‖f n‖)

theorem analyticOnNhd_natL1OfFunction_of_summable_bound
    (f : E → ℕ → ℂ) (U : Set E) (hU : IsOpen U)
    (ha : ∀ n : ℕ, AnalyticOnNhd ℂ (fun x => f x n) U)
    (C : ℝ) (hb : ∀ x∈U, Summable (fun n : ℕ => ‖f x n‖) ∧ (∑' n : ℕ, ‖f x n‖)≤C) :
    AnalyticOnNhd ℂ (fun x => natL1OfFunction (f x)) U := by
  let : Fact (1≤(1:ℝ≥0∞)) := ⟨le_rfl⟩
  have hcoord (j : ℤ) : AnalyticOnNhd ℂ (fun x => natL1OfFunction (f x) j) U := by
    intro x hx
    apply (ha (Equiv.intEquivNat j) x hx).congr
    filter_upwards [hU.mem_nhds hx] with y hy
    have hh := natL1OfFunction_apply_of_summable (f y) (hb y hy).1 (Equiv.intEquivNat j)
    simpa only [Equiv.symm_apply_apply] using hh.symm
  exact analyticOnNhd_of_bounded_coordinatewise _ hU hcoord C (fun x hx =>
    (norm_natL1OfFunction_eq_tsum (f x) (hb x hx).1).le.trans (hb x hx).2)

end NLS.Coeff
