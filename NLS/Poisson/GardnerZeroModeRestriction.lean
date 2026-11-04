import NLS.Poisson.GardnerHamiltonianDirection
import NLS.SequenceSpaces.WeightedZeroMode

/-! The scalar Gardner bracket is intrinsic to the mean-zero source:
adding constant cotangents or changing an ambient extension does not
change it. All equalities concern the actual bounded cotangents. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson

theorem gardnerBivector_congr_nonzero_coefficients
    (a a' b b' : WeightedCoeff (Weight.sobolev 1) 2)
    (ha : ∀ k : ℤ, k ≠ 0 → a.val k=a'.val k)
    (hb : ∀ k : ℤ, k ≠ 0 → b.val k=b'.val k) : gardnerBivector a b=gardnerBivector a' b' := by
  rw [gardnerBivector_eq_tsum,gardnerBivector_eq_tsum]
  apply tsum_congr
  intro k
  by_cases hk : k=0
  · subst k
    simp only [Int.cast_zero,neg_zero,mul_zero,zero_mul]
  · rw [ha k hk,hb (-k) (neg_ne_zero.mpr hk)]

theorem hminusCotangentCLM_eq_nonzero_of_eq_on_mean_zero
    (L M : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ)
    (hLM : ∀ h : WeightedCoeff (Weight.sobolev (-1)) 2, h.val 0=0 → L h=M h)
    (k : ℤ) (hk : k ≠ 0) : (hminusCotangentCLM L).val k=(hminusCotangentCLM M).val k := by
  rw [hminusCotangentCLM_apply,hminusCotangentCLM_apply]
  apply hLM
  simp [WeightedCoeff.ofFinsupp_apply,hk]

theorem gardnerCotangentBivector_eq_of_eq_on_mean_zero
    (L L' M M' : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ)
    (hL : ∀ h : WeightedCoeff (Weight.sobolev (-1)) 2, h.val 0=0 → L h=L' h)
    (hM : ∀ h : WeightedCoeff (Weight.sobolev (-1)) 2, h.val 0=0 → M h=M' h) :
    gardnerCotangentBivector L M=gardnerCotangentBivector L' M' := by
  change gardnerBivector (hminusCotangentCLM L) (hminusCotangentCLM M)=
    gardnerBivector (hminusCotangentCLM L') (hminusCotangentCLM M')
  exact gardnerBivector_congr_nonzero_coefficients _ _ _ _
    (hminusCotangentCLM_eq_nonzero_of_eq_on_mean_zero L L' hL)
    (hminusCotangentCLM_eq_nonzero_of_eq_on_mean_zero M M' hM)

def gardnerZeroModeCotangentExtension
    (L : WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ :=
  L.comp (WeightedCoeff.zeroModeProjection (p := 2) (Weight.sobolev (-1)))

theorem gardnerZeroModeCotangentExtension_restrict
    (L : WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ)
    (h : WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2) :
    gardnerZeroModeCotangentExtension L h.val=L h := by
  change L (WeightedCoeff.zeroModeProjection (p := 2) (Weight.sobolev (-1)) h.val)=L h
  congr 1
  apply Subtype.ext
  exact WeightedCoeff.zeroModeProjection_coe _ _ h.property

def gardnerZeroModeCotangentExtensionCLM :
    (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ]
      (WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :=
  (WeightedCoeff.zeroModeProjection (p := 2) (Weight.sobolev (-1))).precomp ℂ

def gardnerMeanZeroCotangentBivector :
    (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ]
      (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ] ℂ := by
  let B : (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ]
      (WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ] ℂ :=
    gardnerCotangentBivector.comp gardnerZeroModeCotangentExtensionCLM
  let C : (WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ]
      (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.flipₗᵢ ℂ
      (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ)
      (WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) ℂ B
  let D : (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ]
      (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ] ℂ :=
    C.comp gardnerZeroModeCotangentExtensionCLM
  exact ContinuousLinearMap.flipₗᵢ ℂ
    (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ)
    (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) ℂ D

theorem gardnerMeanZeroCotangentBivector_restrict
    (L M : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    gardnerMeanZeroCotangentBivector
      (L.comp (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)
      (M.comp (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)=gardnerCotangentBivector L M := by
  change gardnerCotangentBivector
    ((L.comp (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL).comp
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.sobolev (-1))))
    ((M.comp (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL).comp
      (WeightedCoeff.zeroModeProjection (p := 2) (Weight.sobolev (-1))))=gardnerCotangentBivector L M
  apply gardnerCotangentBivector_eq_of_eq_on_mean_zero
  · intro h hh
    change L (WeightedCoeff.zeroModeProjection (p := 2) (Weight.sobolev (-1)) h).val=L h
    rw [WeightedCoeff.zeroModeProjection_coe _ _ hh]
  · intro h hh
    change M (WeightedCoeff.zeroModeProjection (p := 2) (Weight.sobolev (-1)) h).val=M h
    rw [WeightedCoeff.zeroModeProjection_coe _ _ hh]

end NLS.Poisson
