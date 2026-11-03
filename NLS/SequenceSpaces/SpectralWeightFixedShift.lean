import NLS.SequenceSpaces.SpectralWeightInterpolation
import Mathlib.Tactic

/-! # Fixed shifts and ceiling cutoffs for interpolated spectral weights. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.SpectralWeight

theorem nat_weight_le_fixed_shift_realExtension (w : SpectralWeight) (j : ℕ) (t : ℝ)
    (ht : 0≤t) (hj : (j : ℝ)≤t+2) :
    w (j : ℤ) ≤ w (3 : ℤ)*w.realExtension t := by
  have hf := Nat.lt_floor_add_one t
  have hjr : (j : ℝ)≤(⌊t⌋₊ : ℝ)+3 := by linarith
  have hjN : j≤⌊t⌋₊+3 := by exact_mod_cast hjr
  have hbase : w (⌊t⌋₊ : ℤ)≤w.realExtension t := by
    simpa only [abs_of_nonneg ht] using (w.realExtension_bounds t).1
  calc
    _ ≤ w ((⌊t⌋₊+3 : ℕ) : ℤ) := w.monotone_nat hjN
    _ ≤ w (⌊t⌋₊ : ℤ)*w (3 : ℤ) := by
      simpa only [Nat.cast_add,Nat.cast_ofNat] using w.add_le (⌊t⌋₊ : ℤ) 3
    _ ≤ w.realExtension t*w (3 : ℤ) := mul_le_mul_of_nonneg_right hbase (w.positive 3).le
    _ = _ := mul_comm _ _

theorem ceil_eight_rpow_weight_bound (w : SpectralWeight) (Q a : ℝ) (hQ : 0≤Q) :
    w ((2*⌈8*Q^a⌉₊ : ℕ) : ℤ) ≤ w (3 : ℤ)*w.realExtension (16*Q^a) := by
  apply nat_weight_le_fixed_shift_realExtension w _ _ (by positivity)
  have hh := Nat.ceil_lt_add_one (by positivity : 0≤8*Q^a)
  push_cast
  linarith

end NLS.SpectralWeight
