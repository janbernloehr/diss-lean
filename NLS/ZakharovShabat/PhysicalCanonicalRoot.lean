import NLS.ZakharovShabat.PhysicalPeriodicEndpoints
import NLS.ZakharovShabat.SourcePhysicalActions

/-! # The canonical product from physical spectral endpoints

Principal standard roots and symmetric products use the intrinsic physical
endpoint labels. The product converges with the exact free sign and equals
the root in the established physical action contour integrals.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- The principal standard root formed directly from the physical endpoints. -/
def physicalStandardRoot (u : IntervalPairL2) (n : ℤ) (z : ℂ) : ℂ :=
  normalizedStandardRoot ((physicalPeriodicLeft u n+physicalPeriodicRight u n)/2)
    ((physicalPeriodicRight u n-physicalPeriodicLeft u n)^2) z

/-- The spectral plane with all physical gap segments removed. -/
def physicalSpectralRootDomain (u : IntervalPairL2) : Set ℂ :=
  {z | ∀ n : ℤ, z ∉ segment ℝ (physicalPeriodicLeft u n) (physicalPeriodicRight u n)}

/-- Pair the positive and negative standard-root factors with their signed lattice denominators. -/
def physicalRootPairFactor (u : IntervalPairL2) (z : ℂ) (j : ℕ) : ℂ :=
  let k : ℤ := (j+1 : ℕ)
  (physicalStandardRoot u k z/((Real.pi:ℂ)*k))*
    (physicalStandardRoot u (-k) z/(-((Real.pi:ℂ)*k)))

/-- The intrinsic canonical root: the zero factor times the convergent paired product, with prefactor 2i. -/
def physicalCanonicalProductRoot (u : IntervalPairL2) (z : ℂ) : ℂ :=
  2*Complex.I*physicalStandardRoot u 0 z*∏' j : ℕ, physicalRootPairFactor u z j

/-- The literal symmetric finite product, with denominator one at the zero index. -/
def physicalCanonicalProductRootPartial (N : ℕ) (u : IntervalPairL2) (z : ℂ) : ℂ :=
  2*Complex.I*∏ m ∈ Finset.Icc (-(N:ℤ)) N, physicalStandardRoot u m z/singleSpectralDenominator m

/-- The physical standard root agrees with the source branch, including its sign. -/
theorem physicalStandardRoot_eq_source (u : IntervalPairL2) (n : ℤ) (z : ℂ) :
    physicalStandardRoot u n z = sourceStandardRoot (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) n z := by
  simp only [physicalStandardRoot,(physicalPeriodicEndpoints_eq_source u).1,
    (physicalPeriodicEndpoints_eq_source u).2,sourceStandardRoot,canonicalPeriodicMidpoint,canonicalPeriodicGap]

/-- The physical and source cut complements agree exactly. -/
theorem physicalSpectralRootDomain_eq_source (u : IntervalPairL2) :
    physicalSpectralRootDomain u = sourceCanonicalRootDomain (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) := by
  simp only [physicalSpectralRootDomain,(physicalPeriodicEndpoints_eq_source u).1,
    (physicalPeriodicEndpoints_eq_source u).2,sourceCanonicalRootDomain,sourcePeriodicSegment]

/-- Every physical paired product factor agrees with its source counterpart. -/
theorem physicalRootPairFactor_eq_source (u : IntervalPairL2) (z : ℂ) :
    physicalRootPairFactor u z = sourceStandardRootPairedFactor (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) z := by
  funext j
  simp only [physicalRootPairFactor,physicalStandardRoot_eq_source,sourceStandardRootPairedFactor]

/-- The intrinsic physical product equals the canonical root used in the existing action integrals. -/
theorem physicalCanonicalProductRoot_eq (u : IntervalPairL2) (z : ℂ) :
    physicalCanonicalProductRoot u z = physicalCanonicalRoot u z := by
  simp only [physicalCanonicalProductRoot,physicalStandardRoot_eq_source,physicalRootPairFactor_eq_source,
    physicalCanonicalRoot,sourceCanonicalRoot,sourceStandardRootPairedProduct]

/-- Every symmetric physical cutoff equals the corresponding source partial product. -/
theorem physicalCanonicalProductRootPartial_eq_source (N : ℕ) (u : IntervalPairL2) (z : ℂ) :
    physicalCanonicalProductRootPartial N u z =
      sourceCanonicalRootPartialProduct (by simp) (by norm_num) N (sourcePhysicalL2Equiv.symm u) z := by
  simp only [physicalCanonicalProductRootPartial,physicalStandardRoot_eq_source,sourceCanonicalRootPartialProduct]

/-- The paired physical factors have a convergent infinite product at every spectral parameter. -/
theorem multipliable_physicalRootPairFactor (u : IntervalPairL2) (z : ℂ) :
    Multipliable (physicalRootPairFactor u z) := by
  rw [physicalRootPairFactor_eq_source]
  exact multipliable_sourceStandardRootPairedFactor (by simp) (by norm_num) _ z

/-- The full symmetric finite products converge to the intrinsic physical canonical root. -/
theorem tendsto_physicalCanonicalProductRootPartial (u : IntervalPairL2) (z : ℂ) :
    Filter.Tendsto (fun N => physicalCanonicalProductRootPartial N u z) Filter.atTop
      (nhds (physicalCanonicalProductRoot u z)) := by
  simp only [physicalCanonicalProductRootPartial_eq_source,physicalCanonicalProductRoot_eq,physicalCanonicalRoot]
  exact tendsto_sourceCanonicalRootPartialProduct (by simp) (by norm_num) _ z

/-- On the cut complement, the physical product squares to the discriminant squared minus four. -/
theorem physicalCanonicalProductRoot_sq (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ physicalSpectralRootDomain u) :
    physicalCanonicalProductRoot u z^2 = l2Discriminant u z^2-4 := by
  rw [physicalCanonicalProductRoot_eq]
  exact physicalCanonicalRoot_sq u z ((physicalSpectralRootDomain_eq_source u) ▸ hz)

/-- The free product has the fixed sign -2i sin(z). -/
theorem physicalCanonicalProductRoot_zero (z : ℂ) :
    physicalCanonicalProductRoot 0 z = -2*Complex.I*sin z := by
  rw [physicalCanonicalProductRoot_eq,physicalCanonicalRoot_zero]

/-- The intrinsic canonical root never vanishes away from the physical gaps. -/
theorem physicalCanonicalProductRoot_ne_zero (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ physicalSpectralRootDomain u) : physicalCanonicalProductRoot u z ≠ 0 := by
  rw [physicalCanonicalProductRoot_eq,physicalCanonicalRoot]
  exact sourceCanonicalRoot_ne_zero_off_gaps (by simp) (by norm_num) _ z
    ((physicalSpectralRootDomain_eq_source u) ▸ hz)
/-- The physical action contour uses the intrinsic product and the actual monodromy discriminant. -/
theorem physicalActionContour_eq_productRoot (u : IntervalPairL2) (Γ : PiecewiseC1Loop) :
    physicalActionContour u Γ = (Real.pi:ℂ)⁻¹*Γ.integral
      (fun z => z*deriv (l2Discriminant u) z/physicalCanonicalProductRoot u z) := by
  simp only [physicalActionContour,physicalCanonicalProductRoot_eq]

end NLS.ZakharovShabat
