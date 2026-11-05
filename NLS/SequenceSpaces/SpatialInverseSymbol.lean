import NLS.SequenceSpaces.SignedSobolevGeneratorRegularity
import NLS.SequenceSpaces.NegativeOrderHalfFourierEquiv

/-! Bounded recovery from the physical spatial generator. The zero mode
is removed explicitly; the original2*pi scalar is never rescaled. -/
noncomputable section
open Complex
namespace NLS

def spatialInverseSymbol (k : ℤ) : ℂ := if k=0 then 0 else (I*((2*Real.pi*k:ℝ):ℂ))⁻¹

theorem spatialInverseSymbol_neg (k : ℤ) :
    spatialInverseSymbol (-k)=(starRingEnd ℂ) (spatialInverseSymbol k) := by
  by_cases hk : k=0
  · simp [spatialInverseSymbol,hk]
  · rw [spatialInverseSymbol,if_neg (neg_ne_zero.mpr hk),spatialInverseSymbol,if_neg hk,map_inv₀]
    congr 1
    simp only [map_mul,Int.cast_neg,Complex.conj_I,Complex.conj_ofReal]
    push_cast
    ring

theorem spatialInverseSymbol_generator (k : ℤ) (a : ℂ) :
    spatialInverseSymbol k*(I*((2*Real.pi*k:ℝ):ℂ)*a)=if k=0 then 0 else a := by
  by_cases hk : k=0
  · simp [spatialInverseSymbol,hk]
  · have hc : I*((2*Real.pi*k:ℝ):ℂ) ≠ 0 := mul_ne_zero I_ne_zero
      (Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by exact_mod_cast hk)))
    rw [spatialInverseSymbol,if_neg hk,← mul_assoc,inv_mul_cancel₀ hc,one_mul,if_neg hk]

namespace Weight

theorem signedSobolev_spatialInverse_bound (s : ℝ) (k : ℤ) :
    signedSobolev (s+1) k*‖spatialInverseSymbol k‖ ≤ (1/(2*Real.pi))*signedSobolev s k := by
  by_cases hk : k=0
  · simp only [spatialInverseSymbol,if_pos hk,norm_zero,mul_zero]
    exact mul_nonneg (by positivity) ((signedSobolev s).positive k).le
  · have hkabs : (1:ℝ) ≤ |(k:ℝ)| := by
      exact_mod_cast (show (1:ℤ) ≤ |k| by have h := abs_pos.mpr hk; omega)
    have hp : 0 < |(k:ℝ)| := by linarith
    have hn : ‖I*((2*Real.pi*k:ℝ):ℂ)‖=(2*Real.pi)*|(k:ℝ)| := by
      rw [norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_mul,
        abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos Real.pi_pos]
    rw [spatialInverseSymbol,if_neg hk,norm_inv,hn]
    change (max (1:ℝ) |(k:ℝ)|)^(s+1)*((2*Real.pi)*|(k:ℝ)|)⁻¹ ≤
      (1/(2*Real.pi))*(max (1:ℝ) |(k:ℝ)|)^s
    rw [max_eq_right hkabs,Real.rpow_add hp,Real.rpow_one]
    apply le_of_eq
    field_simp

theorem sobolev_spatialInverse_to_zero_bound (k : ℤ) :
    signedSobolev 0 k*‖spatialInverseSymbol k‖ ≤ (1/Real.pi)*sobolev (-1) k := by
  have hi := signedSobolev_spatialInverse_bound (-1) k
  rw [show (-1:ℝ)+1=0 by norm_num] at hi
  have hc := (signedSobolev_negative_bounds 1 (by norm_num) k).2
  norm_num only [Real.rpow_one] at hc
  calc
    _ ≤ (1/(2*Real.pi))*signedSobolev (-1) k := hi
    _ ≤ (1/(2*Real.pi))*(2*sobolev (-1) k) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by field_simp

end Weight
end NLS
