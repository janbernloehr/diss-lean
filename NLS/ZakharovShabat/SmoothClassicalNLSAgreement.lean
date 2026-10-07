import NLS.ZakharovShabat.SmoothPeriodOneSource
import NLS.ZakharovShabat.SourceClassicalRenormalizedNLSAgreement

/-! # Spectral agreement for arbitrary smooth classical initial data

The initial real H¹ source and its physical mass are constructed from the
actual initial function. No Sobolev representative, finite-gap condition,
or spectral mass equality is supplied by the caller.
-/
noncomputable section
open Set NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The canonical smooth source has exactly the physical initial mass. -/
theorem sourceOrdinaryMass_smoothPeriodOneHilbertSource (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    sourceOrdinaryMass le_rfl (smoothPeriodOneHilbertSource f hf hp) = classicalNLSMass f := by
  have h := sourceOrdinaryMass_sobolevSource (smoothPeriodOneSource f hf hp)
  rw [periodOneSobolevSynthesis_smoothPeriodOneSource] at h
  exact h

namespace SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Every classical ordinary NLS trajectory agrees with the spectral flow
from its actual initial Fourier coefficients. -/
theorem classicalNLS_periodOneCoefficient_eq_smoothFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P s)
    (hP : IsOpen P) (hr : realTypeSourceLocus 2 ⊆ P)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) (hu : IsClassicalNLSTrajectory u) (time : ℝ) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) n =
      (A.hamiltonianOrdinarySourceFlow D le_rfl
        (smoothPeriodOneHilbertSource (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) time).val.fst n := by
  exact A.classicalNLS_periodOneCoefficient_eq_hamiltonianFlow hs hP hr D
    (smoothPeriodOneSource (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) u hu
    (periodOneSobolevSynthesis_smoothPeriodOneSource _ _ _).symm time n

/-- Every classical renormalized trajectory with its physical initial mass
agrees with the renormalized spectral flow from its actual initial coefficients. -/
theorem classicalRenormalizedNLS_periodOneCoefficient_eq_smoothFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P s)
    (hP : IsOpen P) (hr : realTypeSourceLocus 2 ⊆ P)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : IsClassicalRenormalizedNLSTrajectory (classicalNLSMass (u 0)) u) (time : ℝ) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) n =
      (A.hamiltonianRenormalizedSourceFlow D le_rfl
        (smoothPeriodOneHilbertSource (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) time).val.fst n := by
  exact A.classicalRenormalizedNLS_periodOneCoefficient_eq_hamiltonianFlow hs hP hr D
    (smoothPeriodOneSource (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) u hu
    (periodOneSobolevSynthesis_smoothPeriodOneSource _ _ _).symm time n

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
