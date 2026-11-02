import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Algebraic inversion of the signed Cartesian Fourier pair -/
noncomputable section
open Complex
namespace NLS.MKdV

/-- Invert the positive signed Fourier coefficient. -/
theorem cartesianFourier_recover_positive (q r k a b : ℂ) (hq : q^2 = 2) (hkr : k*r = 1) :
    k*(-(r*(-(a+b)/q))+I*(-(r*((a-b)/(q*I)))))/q = b := by
  have hqne : q ≠ 0 := by intro h; rw [h] at hq; norm_num at hq
  calc
    _ = (k*r)*b*(2/q^2) := by field_simp [hqne,I_ne_zero]; ring
    _ = b := by rw [hkr,hq]; norm_num

/-- Invert the negative signed Fourier coefficient. -/
theorem cartesianFourier_recover_negative (q r k a b : ℂ) (hq : q^2 = 2) (hkr : k*r = 1) :
    k*(-(r*(-(a+b)/q))-I*(-(r*((a-b)/(q*I)))))/q = a := by
  have hqne : q ≠ 0 := by intro h; rw [h] at hq; norm_num at hq
  calc
    _ = (k*r)*a*(2/q^2) := by field_simp [hqne,I_ne_zero]; ring
    _ = a := by rw [hkr,hq]; norm_num

/-- The reconstructed two Fourier modes have the prescribed first coordinate. -/
theorem cartesianFourier_recover_first (q r k x y : ℂ) (hq : q^2 = 2) (hkr : k*r = 1) :
    r*(-(k*(-x-I*y)/q+k*(-x+I*y)/q)/q) = x := by
  have hqne : q ≠ 0 := by intro h; rw [h] at hq; norm_num at hq
  calc
    _ = (k*r)*x*(2/q^2) := by field_simp [hqne]; ring
    _ = x := by rw [hkr,hq]; norm_num

/-- The reconstructed two Fourier modes have the prescribed second coordinate. -/
theorem cartesianFourier_recover_second (q r k x y : ℂ) (hq : q^2 = 2) (hkr : k*r = 1) :
    -(r*((k*(-x-I*y)/q-k*(-x+I*y)/q)/(q*I))) = y := by
  have hqne : q ≠ 0 := by intro h; rw [h] at hq; norm_num at hq
  calc
    _ = (k*r)*y*(2/q^2) := by field_simp [hqne,I_ne_zero]; ring
    _ = y := by rw [hkr,hq]; norm_num

end NLS.MKdV
