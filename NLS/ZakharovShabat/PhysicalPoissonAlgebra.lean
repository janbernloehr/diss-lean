import NLS.ZakharovShabat.PhysicalCotangentGradient

/-! # Algebra of the literal physical Poisson pairing

The physical cross-gradient integral is complex bilinear in its actual
continuous cotangents. These laws retain the proved integral/source
comparison and support differentiation of the physical action radii.
-/

noncomputable section
open Set Metric MeasureTheory Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Bilinearity in the first physical cotangent. -/
theorem physicalCotangentBivector_add_left (L M N : IntervalPairL2 →L[ℂ] ℂ) :
    physicalCotangentBivector (L+M) N = physicalCotangentBivector L N+physicalCotangentBivector M N := by
  simp only [physicalCotangentBivector_eq_source,ContinuousLinearMap.add_comp,map_add,
    add_apply]

/-- Bilinearity in the second physical cotangent. -/
theorem physicalCotangentBivector_add_right (L M N : IntervalPairL2 →L[ℂ] ℂ) :
    physicalCotangentBivector L (M+N) = physicalCotangentBivector L M+physicalCotangentBivector L N := by
  simp only [physicalCotangentBivector_eq_source,ContinuousLinearMap.add_comp,map_add]

/-- Complex homogeneity in the first physical cotangent. -/
theorem physicalCotangentBivector_smul_left (c : ℂ) (L M : IntervalPairL2 →L[ℂ] ℂ) :
    physicalCotangentBivector (c • L) M = c*physicalCotangentBivector L M := by
  simp only [physicalCotangentBivector_eq_source,ContinuousLinearMap.smul_comp,map_smul,
    smul_apply,smul_eq_mul]

/-- Complex homogeneity in the second physical cotangent. -/
theorem physicalCotangentBivector_smul_right (c : ℂ) (L M : IntervalPairL2 →L[ℂ] ℂ) :
    physicalCotangentBivector L (c • M) = c*physicalCotangentBivector L M := by
  simp only [physicalCotangentBivector_eq_source,ContinuousLinearMap.smul_comp,map_smul,smul_eq_mul]

end NLS.ZakharovShabat
