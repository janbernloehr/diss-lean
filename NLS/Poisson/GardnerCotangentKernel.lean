import NLS.Poisson.GardnerHamiltonianDirection

/-! The scalar Gardner derivative loses only the constant cotangent mode.
Equal Gardner vectors therefore give equal differentials on the ENTIRE
mean-zero Hminus-one source, not only on finite Fourier directions. -/
noncomputable section
open Complex
namespace NLS.Poisson

theorem gardnerDerivative_eq_implies_nonzero_coordinates
    (a b : WeightedCoeff (Weight.sobolev 1) 2) (he : gardnerDerivative a=gardnerDerivative b)
    (k : ℤ) (hk : k ≠ 0) : a.val k=b.val k := by
  have h := congrArg (fun v : WeightedCoeff (Weight.sobolev (-1)) 2 => v.val k) he
  rw [gardnerDerivative_apply,gardnerDerivative_apply] at h
  have hpi : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast (show (2*Real.pi:ℝ) ≠ 0 by positivity)
  have hkc : (k:ℂ) ≠ 0 := by exact_mod_cast hk
  exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hpi I_ne_zero) hkc) h

/-- Only the zeroth source mode could see the missing constant cotangent;
all series and full Banach directions retain the original Sobolev pairing. -/
theorem sobolevBilinearPairing_eq_of_gardnerDerivative_eq
    (a b : WeightedCoeff (Weight.sobolev 1) 2) (he : gardnerDerivative a=gardnerDerivative b)
    (h : WeightedCoeff (Weight.sobolev (-1)) 2) (h0 : h.val 0=0) :
    WeightedCoeff.sobolevBilinearPairing 1 a h=WeightedCoeff.sobolevBilinearPairing 1 b h := by
  rw [WeightedCoeff.sobolevBilinearPairing_apply,WeightedCoeff.sobolevBilinearPairing_apply]
  apply tsum_congr
  intro k
  by_cases hk : k=0
  · subst k
    rw [neg_zero,h0,mul_zero,mul_zero]
  · rw [gardnerDerivative_eq_implies_nonzero_coordinates a b he k hk]

end NLS.Poisson
