import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # The norm-dependent ceiling cutoff has a quadratic norm bound. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.SequenceSpaces

theorem ceiling_weighted_cutoff_le_quadratic (t r : ℝ) (ht : 0≤t) (hr0 : 0≤r) :
    (⌈8*(max 1 t)^(3/2-r)⌉₊ : ℝ)+1≤10*(1+t)^2 := by
  have hQ : (1 : ℝ)≤max 1 t := le_max_left _ _
  have hQ0 : (0 : ℝ)<max 1 t := zero_lt_one.trans_le hQ
  have hp : (max 1 t)^(3/2-r)≤(max 1 t)^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hQ (by linarith : 3/2-r≤2)
  have hceil := Nat.ceil_lt_add_one (by positivity : 0≤8*(max 1 t)^(3/2-r))
  have hmax : max 1 t≤1+t := max_le (by linarith) (by linarith)
  have hs : (max 1 t)^2≤(1+t)^2 := by nlinarith
  nlinarith [sq_nonneg t]

end NLS.SequenceSpaces
