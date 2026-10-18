import NLS.ZakharovShabat.SourceExteriorQuotientContour
import NLS.ZakharovShabat.SourceExteriorRootDenominator
import NLS.ZakharovShabat.SourceExteriorKernelFiniteSum

/-! # Exterior contours equal the actual positive kernels

Each exterior contour is exactly -2*pi*i times its positive angular
kernel integral, in the original root and action conventions.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- The exterior contour equals minus 2*pi*i times the actual positive kernel integral. -/
theorem filledGapQuotient_exterior_circle_eq_kernel (n m : ℤ) (hmn : m ≠ n)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (hgn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (θ : ℝ) (R : ℝ) (hinner : C.discs.inner m ≤ R) (houter : R < C.discs.outer m) :
    (∮ z in C(C.discs.center m,R), C.filledGapQuotient n φ.val z/
      (z-sourceCanonicalRootGapPoint hp hp1 φ.val n (Real.cos θ))) =
      -(2*(Real.pi:ℂ)*I) * ((∫ η : ℝ,
        sourceExteriorGapKernelWeight hp hp1 φ n (⟨m,hmn⟩,η)/
          |sourceExteriorGapPole hp hp1 φ n (⟨m,hmn⟩,η)-Real.cos θ| : ℝ):ℂ) := by
  have hx := C.segment_subset_outer n φ.val hφ
    (sourceCanonicalRootGapPoint_mem_segment hp hp1 φ.val n (Real.cos θ) (Real.neg_one_le_cos θ) (Real.cos_le_one θ))
  rw [C.filledGapQuotient_exterior_circle_eq_profile n m hmn φ hφ hgap _ hx R hinner houter,
    integral_sourceExteriorGapKernel_eq_interval hp hp1 φ n hgn ⟨m,hmn⟩ θ,
    ← intervalIntegral.integral_ofReal]
  simp only [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro η _
  dsimp only
  rw [sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 φ.val φ.property m,
    sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 φ.val φ.property n]
  rw [sourceStandardRoot_mul_exterior_displacement hp hp1 φ n m hmn _ _
    (realGapAffinePoint_cos_mem_Icc hp hp1 φ n θ) (realGapAffinePoint_cos_mem_Icc hp hp1 φ m η),
    sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 φ.val φ.property m]
  dsimp only [sourceExteriorGapRoot,sourceGapHalfWidthReal]
  push_cast
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
