import NLS.KdV.HillCharacteristicZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! # Exact free Hill characteristic roots and their orders

The actual energy characteristic has a simple zero at zero energy and
double zeros at the positive free lattice. These orders refer to the
normalized physical monodromy trace, including the ramified point zero.
-/

noncomputable section
open Set
namespace NLS.KdV

theorem freeHillValue_natAbs (k : ℤ) : freeHillValue (k.natAbs : ℕ) = freeHillValue k := by
  unfold freeHillValue
  rw [Int.natCast_natAbs, Int.cast_abs, sq_abs]

theorem strictMono_freeHillValue : StrictMono (fun n : ℕ => freeHillValue n) := by
  intro m n hmn
  have hsq : (m : ℝ)^2 < (n : ℝ)^2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mpr (by exact_mod_cast hmn)
  exact mul_lt_mul_of_pos_left hsq (sq_pos_of_pos Real.pi_pos)

/-- The complete zero set of the actual free Hill characteristic. -/
theorem hillL2Radicand_free_zero_iff (lambda : ℂ) :
    hillL2Radicand 0 lambda = 0 ↔ ∃ n : ℕ, lambda = (freeHillValue n : ℂ) := by
  constructor
  · intro hd
    rw [hillL2Radicand_zero] at hd
    have hs : Complex.sin (Complex.sqrt lambda) = 0 :=
      eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hd).resolve_left (by norm_num))
    obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hs
    refine ⟨k.natAbs,?_⟩
    rw [freeHillValue_natAbs]
    have h := ComplexAnalysis.complex_sqrt_sq lambda
    rw [hk] at h
    rw [← h]
    simp only [freeHillValue, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_intCast]
    ring
  · rintro ⟨n,rfl⟩
    have hs : Complex.sqrt (freeHillValue n : ℂ)^2 = ((n : ℂ)*(Real.pi : ℂ))^2 := by
      rw [ComplexAnalysis.complex_sqrt_sq]
      simp only [freeHillValue, Int.cast_natCast, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_natCast]
      ring
    rw [hillL2Radicand_zero]
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with h | h <;>
      simp [h, Complex.sin_nat_mul_pi]

/-- The zero energy is simple in energy, although frequency is ramified there. -/
theorem hillL2Radicand_free_order_zero : analyticOrderNatAt (hillL2Radicand 0) 0 = 1 := by
  have ha : AnalyticAt ℂ (hillL2Radicand 0) 0 := analyticOnNhd_hillL2Radicand 0 0 (mem_univ _)
  have hs : analyticOrderAt Complex.sin 0 = 1 :=
    Complex.analyticAt_sin.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (by simp) (by simp [Complex.deriv_sin])
  have hc : analyticOrderAt (fun _ : ℂ => (-4 : ℂ)) 0 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (by norm_num))
  have hf : (fun z : ℂ => hillL2Radicand 0 (z^2)) = fun z : ℂ => (-4 : ℂ)*Complex.sin z^2 := by
    funext z
    rw [hillL2Radicand_zero]
    have hroot := ComplexAnalysis.complex_sqrt_sq (z^2)
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hroot with h | h <;> simp [h]
  have hcomp : analyticOrderAt (fun z : ℂ => hillL2Radicand 0 (z^2)) 0 = 2 := by
    rw [hf]
    change analyticOrderAt ((fun _ : ℂ => (-4 : ℂ))*Complex.sin^2) 0 = 2
    rw [analyticOrderAt_mul analyticAt_const (Complex.analyticAt_sin.pow 2),
      analyticOrderAt_pow Complex.analyticAt_sin, hs, hc]
    norm_num
  have ha' : AnalyticAt ℂ (hillL2Radicand 0) ((0 : ℂ)^2) := by simpa using ha
  have horder := ha'.analyticOrderAt_comp (show AnalyticAt ℂ (fun z : ℂ => z^2) 0 by fun_prop)
  have hg : analyticOrderAt (fun z : ℂ => z^2-(0 : ℂ)^2) 0 = 2 := by
    have he : (fun z : ℂ => z^2-(0 : ℂ)^2) = ((·-(0 : ℂ))^2) := by
      funext z
      simp
    rw [he]
    exact analyticOrderAt_centeredMonomial
  change analyticOrderAt (fun z : ℂ => hillL2Radicand 0 (z^2)) 0 =
    analyticOrderAt (hillL2Radicand 0) ((0 : ℂ)^2)*_ at horder
  rw [hcomp, hg] at horder
  norm_num only [zero_pow (by norm_num : 2 ≠ 0)] at horder
  have hfinite : analyticOrderAt (hillL2Radicand 0) 0 ≠ ⊤ := by
    intro htop
    rw [htop] at horder
    norm_num at horder
  lift analyticOrderAt (hillL2Radicand 0) 0 to ℕ using hfinite with k hk
  have he : 2 = k*2 := by exact_mod_cast horder
  have hk1 : k = 1 := by omega
  change (analyticOrderAt (hillL2Radicand 0) 0).toNat = 1
  rw [← hk, hk1]
  rfl

end NLS.KdV
