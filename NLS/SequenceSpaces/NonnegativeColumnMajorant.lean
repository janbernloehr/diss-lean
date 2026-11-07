import NLS.SequenceSpaces.FunctionOrZero
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Uniform summable nonnegative columns produce an actual ell1
majorant vector. Tonelli justifies both row sums and the full vector
norm before any output index is chosen. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem exists_one_of_nonnegative_column_bound
    (L : ℤ → ℤ → ℝ) (hL : ∀ n k, 0≤L n k)
    (C : ℝ) (hcol : ∀ k, Summable (fun n => L n k))
    (hbound : ∀ k, (∑' n, L n k)≤C) (b : Coeff 1) :
    ∃ a : Coeff 1, (∀ n, Summable (fun k => L n k*‖b k‖)) ∧
      (∀ n, a n=((∑' k, L n k*‖b k‖ : ℝ) : ℂ)) ∧ ‖a‖≤C*‖b‖ := by
  have hb : Summable (fun k : ℤ => ‖b k‖) := (lp.memℓp b).norm.summable_of_one
  have hc (k : ℤ) : Summable (fun n : ℤ => L n k*‖b k‖) := (hcol k).mul_right ‖b k‖
  have hcs : Summable (fun k : ℤ => ∑' n : ℤ, L n k*‖b k‖) := by
    apply (hb.mul_left C).of_nonneg_of_le (fun k => tsum_nonneg (fun n => mul_nonneg (hL n k) (norm_nonneg _)))
    intro k
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hbound k) (norm_nonneg _)
  have hprod : Summable (fun p : ℤ × ℤ => L p.2 p.1*‖b p.1‖) :=
    (summable_prod_of_nonneg (fun p => mul_nonneg (hL p.2 p.1) (norm_nonneg _))).mpr ⟨hc,hcs⟩
  obtain ⟨hrow,hrows⟩ := (summable_prod_of_nonneg
    (fun p : ℤ × ℤ => mul_nonneg (hL p.1 p.2) (norm_nonneg (b p.2)))).mp hprod.prod_symm
  let f := fun n : ℤ => ((∑' k, L n k*‖b k‖ : ℝ) : ℂ)
  have hfn (n : ℤ) : ‖f n‖=∑' k, L n k*‖b k‖ :=
    Complex.norm_of_nonneg (tsum_nonneg (fun k => mul_nonneg (hL n k) (norm_nonneg _)))
  have hm : Memℓp f 1 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one,Real.rpow_one,hfn] using hrows
  let a : Coeff 1 := ⟨f,hm⟩
  refine ⟨a,hrow,fun _ => rfl,?_⟩
  have han : ‖a‖=∑' n : ℤ, ∑' k : ℤ, L n k*‖b k‖ := by
    simpa only [a,hfn,ENNReal.toReal_one,Real.rpow_one] using (lp.hasSum_norm (p := 1) (by simp) a).tsum_eq.symm
  have he : (∑' k : ℤ, ∑' n : ℤ, L n k*‖b k‖)=(∑' n : ℤ, ∑' k : ℤ, L n k*‖b k‖) :=
    (Summable.tsum_comm (f := fun k n : ℤ => L n k*‖b k‖) hprod).symm
  rw [han,←he]
  calc
    _≤∑' k : ℤ, C*‖b k‖ := hcs.tsum_le_tsum (fun k => by
      rw [tsum_mul_right]
      exact mul_le_mul_of_nonneg_right (hbound k) (norm_nonneg _)) (hb.mul_left C)
    _=C*‖b‖ := by
      rw [tsum_mul_left]
      congr 1
      simpa only [ENNReal.toReal_one,Real.rpow_one] using (lp.hasSum_norm (p := 1) (by simp) b).tsum_eq

end NLS.Coeff
