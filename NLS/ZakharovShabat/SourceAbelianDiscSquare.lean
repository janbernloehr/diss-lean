import NLS.ComplexAnalysis.GapPrimitiveSquare
import NLS.ZakharovShabat.SourceAbelianGapBoundary

/-! # Analytic squares of normalized abelian disc primitives

The selected standard root carries the only cut in an isolating disc.
Its regular numerator is analytic there. The general squared-primitive
extension therefore applies to the actual discriminant quotient.
-/
noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianDiscPrimitive
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p}
  {hφ : IsRealType (CoeffPair.toMax p φ)} {n : ℤ}

/-- The square of the normalized disc primitive, with the selected
cut filled by its unique analytic extension. -/
def squareExtension (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) : ℂ → ℂ :=
  gapPrimitiveSquareExtension D.toFun
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)

/-- All points of the selected gap, including both endpoints and the
collapsed case, belong to the analytic domain of the square. -/
theorem squareExtension_spec (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    AnalyticOnNhd ℂ D.squareExtension (ball D.center D.radius) ∧
      EqOn D.squareExtension (fun z => D.toFun z^2)
        (ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ n) ∧
      D.squareExtension (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) = 0 ∧
      D.squareExtension (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) = 0 := by
  obtain ⟨W,_,hWreal,hE⟩ := exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  have hg : AnalyticOnNhd ℂ (sourceCriticalRootGapNumerator hp hp1 φ n) (ball D.center D.radius) := by
    intro z hz
    exact (analyticAt_const.sub analyticAt_id).mul
      (hE φ (hWreal hφ) n z (D.avoids_other (ball_subset_closedBall hz)))
  apply gapPrimitiveSquareExtension_spec (sourceCriticalRootGapNumerator hp hp1 φ n)
    (sourceStandardRoot hp hp1 φ n) D.toFun (ball D.center D.radius) _ _
    isOpen_ball D.segment_subset hg
  · intro z hz
    exact (sourceStandardRoot_analyticAt hp hp1 φ n z hz.2).continuousAt.continuousWithinAt
  · intro z hz
    exact sourceStandardRoot_sq_of_not_mem_segment hp hp1 φ n z hz.2
  · intro z hz
    have hroot := sourceAbelian_discComplement_subset_rootDomain hp hp1 φ n D.center D.radius D.avoids_other hz
    have heq : deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z =
        sourceCriticalRootGapNumerator hp hp1 φ n z / sourceStandardRoot hp hp1 φ n z := by
      rw [sourceCriticalRootRatio_eq_selectedFactor_mul_extension hp hp1 φ n z hroot]
      unfold sourceCriticalRootGapNumerator
      simp only [div_eq_mul_inv]
      ring
    rw [← heq]
    exact D.hasDerivAt z hz
  · exact D.left_limit
  · exact D.right_limit

/-- Away from the cuts the disc square is exactly the square of the
filled global primitive with its signed-index normalization. -/
theorem squareExtension_eq_global_of_mem_rootDomain
    (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) (z : ℂ)
    (hz : z ∈ ball D.center D.radius) (hroot : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    D.squareExtension z = (sourceAbelianPrimitive hp hp1 φ hφ z+I*(Real.pi : ℂ)*n)^2 := by
  have hd : z ∈ ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ n := ⟨hz,hroot n⟩
  rw [D.squareExtension_spec.2.1 hd,sourceAbelianPrimitive_eq_global hp hp1 φ hφ hroot,
    sourceAbelianGlobalPrimitive_eq_disc hp hp1 φ hφ n D (Or.inr hd)]
  change D.toFun z^2 = (D.extension z-I*(Real.pi : ℂ)*n+I*(Real.pi : ℂ)*n)^2
  rw [sub_add_cancel,D.extension_eq_disc hd]

end NLS.ZakharovShabat.SourceAbelianDiscPrimitive
