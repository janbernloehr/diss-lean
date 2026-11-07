import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Units.Basic

/-! # Equality on one period determines an invertible Floquet continuation -/
open Set
namespace NLS.FunctionalAnalysis
variable {R : Type} [Monoid R]

theorem floquet_eq_of_unit_period (F G : ℝ → R) (T : Rˣ)
    (hF : ∀ x : ℝ, F (x+1) = F x*(T:R))
    (hG : ∀ x : ℝ, G (x+1) = G x*(T:R))
    (hunit : ∀ t : Icc (0:ℝ) 1, F t = G t) : F = G := by
  have hcancel {a b : R} (h : a*(T:R) = b*(T:R)) : a = b := by
    have he : (T:R)*(↑(T⁻¹):R) = 1 := by
      exact Units.mul_inv T
    have hh := congrArg (fun c : R => c*(↑(T⁻¹):R)) h
    simpa only [mul_assoc,he,mul_one] using hh
  have hn (t : Icc (0:ℝ) 1) (n : ℤ) : F (t.val+n) = G (t.val+n) := by
    induction n using Int.induction_on with
    | zero => simpa only [Int.cast_zero,add_zero] using hunit t
    | succ n ih =>
      have he : t.val+(↑(n+1 : ℤ):ℝ) = (t.val+n)+1 := by push_cast; ring
      rw [he,hF,hG]
      simpa only [Int.cast_natCast] using congrArg (fun v : R => v*(T:R)) ih
    | pred n ih =>
      apply hcancel
      rw [← hF,← hG]
      have he : t.val+(↑(-(n:ℤ)-1):ℝ)+1 = t.val+(-(n:ℤ):ℝ) := by push_cast; ring
      rw [he]
      simpa only [Int.cast_neg,Int.cast_natCast] using ih
  funext x
  have h := hn ⟨Int.fract x,Int.fract_nonneg x,(Int.fract_lt_one x).le⟩ ⌊x⌋
  simpa only [Int.fract_add_floor] using h

end NLS.FunctionalAnalysis
