import NLS.ZakharovShabat.SourcePQSplitting

/-! # The transformed complementary equation and the original free resolvent

The Q equation on the actual derivative domain gives `(Id-T) Φv=T Φu`
without requiring a small potential or large frequency. Its reconstruction
under the usual inverse hypothesis remains in `WeightedQEquation`. Away
from the free lattice, the complementary inverse agrees with the original
free resolvent applied to the complementary projection.
-/

noncomputable section
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Q equation implies the printed Id-T identity without any smallness assumption. -/
theorem sourceQEquation_transformed (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (u v : WeightedDomain w.toWeight p)
    (hv : complementaryProjection w.toWeight.oneDerivative n v = v)
    (he : weightedFreePencil w.toWeight z v =
      complementaryProjection w.toWeight n (weightedDomainPotential hp w φ (u+v))) :
    weightedDomainPotential hp w φ v -
      weightedPotentialInverse hp w φ n z hz (weightedDomainPotential hp w φ v) =
        weightedPotentialInverse hp w φ n z hz (weightedDomainPotential hp w φ u) := by
  have hvR := complementaryFreeDomainInverse_unique w.toWeight n z hz
    (weightedDomainPotential hp w φ (u+v)) v hv he
  have hPhi : weightedDomainPotential hp w φ v =
      weightedPotentialInverse hp w φ n z hz (weightedDomainPotential hp w φ (u+v)) := by
    exact (congrArg (weightedDomainPotential hp w φ) hvR).trans
      (weightedDomainPotential_complementaryInverse _ _ _ _ _ _ _)
  apply sub_eq_iff_eq_add.mpr
  simpa only [map_add] using hPhi

/-- Off the free lattice, the original free resolvent on Q agrees with the actual weighted complementary inverse. -/
theorem sourceFreeResolvent_complementary (hp : p ≠ ⊤) (w : SpectralWeight)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (hz0 : z ∉ freeLattice)
    (f : WeightedCoeffPair w.toWeight p) :
    sourceFreeResolvent hp z hz0
      (sourceWeightedPeriodTwoInput w (complementaryProjection w.toWeight n f)) =
        sourceWeightedPeriodTwoInput w (complementaryFreeInverse w.toWeight n z hz f) := by
  rw [← sourceResolvent_zero_eq_free hp z hz0,sourceResolvent_eq_inclusion_comp]
  change sourceDomainInclusion (sourceResolventToDomain hp 0 z _) = _
  rw [← sourceComplementaryFreeInverse_equation hp w n z hz f,
    sourceResolventToDomain_sourceSpectralPencil hp 0 z (mem_sourceResolventSet_zero_of_notMem hp z hz0),
    sourceWeightedDomainInput_inclusion,include_complementaryFreeDomainInverse]

end NLS.ZakharovShabat
