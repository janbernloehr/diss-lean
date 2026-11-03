import NLS.SequenceSpaces.SpectralWeightFixedShift
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Ceiling cutoffs preserve the exact interpolated source weight argument. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.SpectralWeight

theorem ceiling_cutoff_weight_le (w : SpectralWeight) (t a : ℝ) (ht : 0≤t) :
    w ((2*⌈8*(max 1 t)^a⌉₊ : ℕ) : ℤ) ≤
      w (16 : ℤ)*w (3 : ℤ)*w.realExtension (16*t^a) := by
  by_cases hlarge : 1≤t
  · rw [max_eq_right hlarge]
    have h := w.ceil_eight_rpow_weight_bound t a ht
    have hnonneg : 0≤w (3 : ℤ)*w.realExtension (16*t^a) := mul_nonneg (w.positive 3).le (w.realExtension_pos _).le
    have hmore := mul_le_mul_of_nonneg_right (w.one_le 16) hnonneg
    nlinarith
  · rw [max_eq_left (by linarith : t≤1),Real.one_rpow]
    norm_num only [mul_one,Nat.ceil_ofNat,Nat.reduceMul,Nat.cast_ofNat]
    have hp : 1≤w (3 : ℤ)*w.realExtension (16*t^a) :=
      by
        have hh := mul_le_mul (w.one_le 3) (w.one_le_realExtension (16*t^a)) (by norm_num : (0 : ℝ)≤1) (w.positive 3).le
        simpa only [one_mul] using hh
    have hh := mul_le_mul_of_nonneg_left hp (w.positive 16).le
    nlinarith

end NLS.SpectralWeight
