import NLS.ZakharovShabat.SourceSobolevFourthLowerHamiltonians
import NLS.ZakharovShabat.PeriodOneSobolevMomentumSymmetry

/-! # The physical H₂ shift vanishes on the original mKdV diagonal

Both components are compared in their actual original Fourier coefficients.
The bounded H¹ inclusion preserves that equality, so the independently
defined physical momentum vanishes on the entire fractional diagonal.
-/
noncomputable section
set_option autoImplicit false
namespace NLS.ZakharovShabat

/-- The physical H¹ inclusion retains equality of the original diagonal fields. -/
theorem fourthNativeH1PairCLM_components_eq_of_diagonal (a : NativeFourthSobolevSource)
    (ha : (originalWeightedRealSource fourthSobolevSpectralWeight a).val.fst =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.snd) :
    (fourthNativeH1PairCLM a).1 = (fourthNativeH1PairCLM a).2 := by
  apply Subtype.ext
  funext n
  exact (fourthNativeH1PairCLM_fst a n).trans
    ((congrArg (fun b : Coeff 2 => b n) ha).trans (fourthNativeH1PairCLM_snd a n).symm)

/-- The original physical H₂ is zero on the full native H^(3/2) mKdV diagonal,
not only at finite-gap or finite Fourier sources. -/
theorem sourceFourthSobolevMomentum_eq_zero_of_diagonal (a : NativeFourthSobolevSource)
    (ha : (originalWeightedRealSource fourthSobolevSpectralWeight a).val.fst =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.snd) :
    sourceFourthSobolevMomentum a = 0 := by
  have he := fourthNativeH1PairCLM_components_eq_of_diagonal a ha
  unfold sourceFourthSobolevMomentum
  have hp : fourthNativeH1PairCLM a = ((fourthNativeH1PairCLM a).1,(fourthNativeH1PairCLM a).1) :=
    Prod.ext rfl he.symm
  rw [hp]
  exact periodOneSobolevMomentum_diagonal _

end NLS.ZakharovShabat
