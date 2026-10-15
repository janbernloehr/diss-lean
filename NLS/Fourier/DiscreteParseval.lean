import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Exact discrete Fourier orthogonality and Parseval

For the unnormalized negative-phase transform on ZMod N, the adjoint is the
reflected transform and the squared ℓ² norm is multiplied by N. These identities
include N=1 and provide the exact Hilbert endpoint for finite interpolation.
-/

noncomputable section
open Finset Complex
open scoped ComplexConjugate ENNReal
namespace NLS.Fourier
variable {N : ℕ} [NeZero N]

/-- Character sums vanish except at zero frequency. -/
theorem sum_stdAddChar_mul (t : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (t*k) = if t = 0 then (N:ℂ) else 0 := by
  classical
  split_ifs with ht
  · simp only [ht,zero_mul,AddChar.map_zero_eq_one,sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_one]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ht)

/-- The adjoint of the negative-phase transform is the reflected transform. -/
theorem sum_dft_adjoint (f g : ZMod N → ℂ) :
    (∑ k : ZMod N, conj (ZMod.dft f k)*g k) = ∑ j : ZMod N, conj (f j)*ZMod.dft g (-j) := by
  classical
  simp only [ZMod.dft_apply,smul_eq_mul,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [← AddChar.map_neg_eq_conj,neg_neg]
  rw [show -(k * -j) = j*k by ring]
  ring

/-- Discrete Parseval for two different complex inputs. -/
theorem sum_dft_mul_conj (f g : ZMod N → ℂ) :
    (∑ k : ZMod N, conj (ZMod.dft f k)*ZMod.dft g k) = (N:ℂ)*∑ j : ZMod N, conj (f j)*g j := by
  rw [sum_dft_adjoint,ZMod.dft_dft]
  simp only [neg_neg,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
/-- Exact energy identity for the unnormalized transform. -/
theorem sum_norm_sq_dft (f : ZMod N → ℂ) :
    (∑ k : ZMod N, ‖ZMod.dft f k‖^2) = (N:ℝ)*∑ j : ZMod N, ‖f j‖^2 := by
  have h := sum_dft_mul_conj f f
  simp_rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq] at h
  have h' := congrArg Complex.re h
  simpa only [map_sum,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] using h'
/-- Each transformed coefficient satisfies the sharp ℓ¹ bound. -/
theorem norm_dft_le_sum_norm (f : ZMod N → ℂ) (k : ZMod N) :
    ‖ZMod.dft f k‖ ≤ ∑ j, ‖f j‖ := by
  rw [ZMod.dft_apply]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simp [ZMod.stdAddChar_apply,Circle.norm_coe]

/-- The exact Hilbert norm factor is √N. -/
theorem norm_dft_piLp_two (f : ZMod N → ℂ) :
    ‖WithLp.toLp 2 (ZMod.dft f)‖ = Real.sqrt N * ‖WithLp.toLp 2 f‖ := by
  rw [PiLp.norm_eq_sum (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
    PiLp.norm_eq_sum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  rw [sum_norm_sq_dft,Real.mul_rpow (Nat.cast_nonneg N) (Finset.sum_nonneg (fun j _ => sq_nonneg ‖f j‖)),
    Real.sqrt_eq_rpow]

end NLS.Fourier
