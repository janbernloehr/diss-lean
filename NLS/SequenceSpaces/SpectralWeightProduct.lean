import NLS.SequenceSpaces.SpectralWeight
import Mathlib.Tactic

/-! # Products of source spectral weights and Sobolev lower bounds. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.SpectralWeight

def product (w v : SpectralWeight) : SpectralWeight where
  value n := w n*v n
  positive n := mul_pos (w.positive n) (v.positive n)
  one_le n := by
    have h := mul_le_mul (w.one_le n) (v.one_le n) (by norm_num : (0 : ℝ)≤1) (w.positive n).le
    simpa only [one_mul] using h
  neg_eq n := by rw [w.apply_neg,v.apply_neg]
  add_le m n := by
    calc
      _ ≤ (w m*w n)*(v m*v n) :=
        mul_le_mul (w.add_le m n) (v.add_le m n) (v.positive (m+n)).le (mul_nonneg (w.positive m).le (w.positive n).le)
      _ = _ := by ring
  monotone_nat m n hmn :=
    mul_le_mul (w.monotone_nat hmn) (v.monotone_nat hmn) (v.positive _).le (w.positive _).le

@[simp] theorem product_apply (w v : SpectralWeight) (n : ℤ) : product w v n=w n*v n := rfl

theorem sobolev_product_dominates (v : SpectralWeight) (r : ℝ) (hr : 0≤r) (m : ℕ) :
    (m : ℝ)^r ≤ product (sobolev r hr) v (2*(m : ℤ)) := by
  rw [product_apply,sobolev_apply,Weight.sobolev_apply]
  have hbase : (m : ℝ)≤1+|((2*(m : ℤ) : ℤ) : ℝ)| := by
    push_cast
    rw [abs_of_nonneg (by positivity : 0≤2*(m : ℝ))]
    linarith
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg m) hbase hr
  have hmul := mul_le_mul_of_nonneg_left (v.one_le (2*(m : ℤ)))
    (Real.rpow_nonneg (by positivity : 0≤1+|((2*(m : ℤ) : ℤ) : ℝ)|) r)
  exact hpow.trans (by simpa only [mul_one] using hmul)

end NLS.SpectralWeight
