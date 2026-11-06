import NLS.SequenceSpaces.LocallyBoundedRealization
import Mathlib.Logic.Equiv.Nat

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.Coeff



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Realize a natural-index sequence in the existing complex Hilbert space,
using a fixed bijection of index sets. -/
def natL2OfFunction (f : ℕ → ℂ) : Coeff 2 :=
  ofFunctionOrZero 2 (fun j : ℤ => f (Equiv.intEquivNat j))

theorem natL2OfFunction_apply_of_summable_sq (f : ℕ → ℂ)
    (hf : Summable (fun n => ‖f n‖^2)) (n : ℕ) :
    natL2OfFunction f (Equiv.intEquivNat.symm n)=f n := by
  have hs : Summable (fun j : ℤ => ‖f (Equiv.intEquivNat j)‖^2) :=
    Equiv.intEquivNat.summable_iff.mpr hf
  have hm : Memℓp (fun j : ℤ => f (Equiv.intEquivNat j)) 2 := by
    rw [memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hs
  rw [natL2OfFunction,ofFunctionOrZero_apply_of_mem 2 _ hm,Equiv.apply_symm_apply]

theorem norm_natL2OfFunction_sq_eq_tsum (f : ℕ → ℂ)
    (hf : Summable (fun n => ‖f n‖^2)) :
    ‖natL2OfFunction f‖^2=∑' n : ℕ, ‖f n‖^2 := by
  have hn (j : ℤ) : natL2OfFunction f j=f (Equiv.intEquivNat j) := by
    have hh := natL2OfFunction_apply_of_summable_sq f hf (Equiv.intEquivNat j)
    simpa only [Equiv.symm_apply_apply] using hh
  have he := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) (natL2OfFunction f)
  calc
    _ = ∑' j : ℤ, ‖f (Equiv.intEquivNat j)‖^2 := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,hn] using he
    _ = _ := Equiv.intEquivNat.tsum_eq (fun n : ℕ => ‖f n‖^2)

/-- Locally bounded square sums and scalar analyticity give the actual
natural-index complex Hilbert analytic sequence, with no fallback on the domain. -/
theorem analyticOnNhd_natL2OfFunction_of_summable_sq_bound
    (f : E → ℕ → ℂ) (U : Set E) (hU : IsOpen U)
    (ha : ∀ n : ℕ, AnalyticOnNhd ℂ (fun x => f x n) U)
    (C : ℝ) (hb : ∀ x∈U, Summable (fun n : ℕ => ‖f x n‖^2) ∧
      (∑' n : ℕ, ‖f x n‖^2)≤C) :
    AnalyticOnNhd ℂ (fun x => natL2OfFunction (f x)) U := by
  have hcoord (j : ℤ) : AnalyticOnNhd ℂ (fun x => natL2OfFunction (f x) j) U := by
    intro x hx
    apply (ha (Equiv.intEquivNat j) x hx).congr
    filter_upwards [hU.mem_nhds hx] with y hy
    have hh := natL2OfFunction_apply_of_summable_sq (f y) (hb y hy).1 (Equiv.intEquivNat j)
    simpa only [Equiv.symm_apply_apply] using hh.symm
  apply analyticOnNhd_of_bounded_coordinatewise _ hU hcoord (Real.sqrt C)
  intro x hx
  have hh : ‖natL2OfFunction (f x)‖^2≤C :=
    (norm_natL2OfFunction_sq_eq_tsum _ (hb x hx).1).le.trans (hb x hx).2
  have hC : 0≤C := (sq_nonneg _).trans hh
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mp
  rwa [Real.sq_sqrt hC]

end NLS.Coeff
