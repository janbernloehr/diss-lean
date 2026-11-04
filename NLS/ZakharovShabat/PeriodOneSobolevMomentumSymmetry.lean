import NLS.ZakharovShabat.PeriodOneSobolevMomentum

/-! # Physical momentum under component exchange

The exact signed Fourier formula gives antisymmetry on the entire H¹ pair
space, hence vanishing on the true equal-component diagonal. No spectral
support or angle symmetry assumption is used.
-/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.ZakharovShabat

/-- The independently defined physical H₂ is antisymmetric under exchange
of its actual H¹ fields. -/
theorem periodOneSobolevMomentum_swap (a b : ScalarDomain 2) :
    periodOneSobolevMomentum (b,a) = -periodOneSobolevMomentum (a,b) := by
  rw [periodOneSobolevMomentum_eq_tsum,periodOneSobolevMomentum_eq_tsum,← tsum_neg]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => (2*(Real.pi:ℂ)*n)*b.val (-n)*a.val n)]
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply,neg_neg,Int.cast_neg]
  ring

/-- The physical momentum vanishes on the whole H¹ mKdV diagonal. -/
theorem periodOneSobolevMomentum_diagonal (a : ScalarDomain 2) :
    periodOneSobolevMomentum (a,a) = 0 := by
  have h := periodOneSobolevMomentum_swap a a
  linear_combination (1/2:ℂ)*h

end NLS.ZakharovShabat
