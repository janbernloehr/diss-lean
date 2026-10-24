import NLS.ZakharovShabat.SymmetricSourceCoordinates
import NLS.ZakharovShabat.SourceClosedGapsZero

/-! # The exact zero fiber of the actual symmetric signed-gap map

Closing every actual periodic gap characterizes the zero real source.
Together with the actual signed-gap identities and the injective real
Fourier parametrization this gives a singleton zero fiber, at every finite
source exponent above one. No global injectivity away from zero follows.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual symmetric signed-gap map sends the zero source to zero for every finite p>1. -/
theorem symmetricSourceSignedGapMap_zero_of_finite (hp : p ≠ ⊤) (hp1 : 1 < p) :
    symmetricSourceSignedGapMap hp hp1 0 = 0 := by
  ext n
  simp [symmetricSourceSignedGapMap,sourceSignedGapSequence_apply,
    canonicalPeriodOneBoundaryRoots_zero]

/-- The zero signed-gap fiber contains only the zero source, for every finite p>1. -/
theorem symmetricSourceSignedGapMap_eq_zero_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : RealCoeff p) : symmetricSourceSignedGapMap hp hp1 a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    let φ := symmetricRealSourceCoefficients p a
    have hs (n : ℤ) : sourceSignedGapSequence hp hp1 φ.val n = 0 := by
      apply Complex.ext
      · exact congrArg (fun b : RealCoeff p => b n) ha
      · exact sourceSignedGapSequence_im_eq_zero hp hp1 φ n
    have hg (n : ℤ) : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem _) n = 0 := by
      have he := sourceSignedGapSequence_sq_of_reflection_fixed hp hp1 φ
        (symmetricRealSourceCoefficients_reflection_fixed a) n
      rw [hs n,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at he
      exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp he.symm
    have hφ := (real_source_all_gaps_closed_iff_zero hp hp1 φ).mp hg
    apply symmetricRealSourceCoefficients_injective
    simpa only [map_zero] using hφ
  · rintro rfl
    exact symmetricSourceSignedGapMap_zero_of_finite hp hp1

/-- The preimage of zero is exactly the singleton zero coordinate. -/
theorem symmetricSourceSignedGapMap_zero_fiber (hp : p ≠ ⊤) (hp1 : 1 < p) :
    (symmetricSourceSignedGapMap hp hp1) ⁻¹' {0} = {0} := by
  ext a
  exact symmetricSourceSignedGapMap_eq_zero_iff hp hp1 a

end NLS.ZakharovShabat
