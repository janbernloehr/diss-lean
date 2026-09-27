import NLS.ZakharovShabat.SourceNormalizedActionCollapsedReal
import NLS.ZakharovShabat.CanonicalCriticalFree
import NLS.ZakharovShabat.DeletedPeriodicFree

/-!
# Free normalization of the complex normalized action

At zero source, every periodic gap collapses and both deleted
products have the same free linear factors. Their quotient is one,
fixing the normalized action at one quarter for every index.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The standard root at zero source is the free linear factor. -/
theorem sourceStandardRoot_zero_source
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (z : ℂ) :
    sourceStandardRoot hp hp1 (0 : CoeffPair p) m z =
      (Real.pi : ℂ)*m-z := by
  unfold sourceStandardRoot
  simp only [map_zero]
  simp only [canonicalPeriodicMidpoint_zero,canonicalPeriodicGap_zero,
    zero_pow (by norm_num : (2:ℕ) ≠ 0),normalizedStandardRoot_zeroGap]

/-- The finite free omitted root product equals the finite free
deleted critical product, factor by factor. -/
theorem sourceStandardRootOmittedPartialProduct_zero_source_eq_deleted
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (N : ℕ) (z : ℂ) :
    sourceStandardRootOmittedPartialProduct hp hp1 n N
      (z,(0 : CoeffPair p)) =
    jointDeletedSingleSpectralPartialProduct n N (z,(0 : Coeff p)) := by
  unfold sourceStandardRootOmittedPartialProduct
    jointDeletedSingleSpectralPartialProduct
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  rw [sourceStandardRoot_zero_source hp hp1 m z]
  simp [singleSpectralFactor,displacedRoots]

/-- The entire free omitted root product equals the free deleted
critical product, including at the removed root. -/
theorem sourceStandardRootOmittedProduct_zero_source_eq_deleted
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (z : ℂ) :
    sourceStandardRootOmittedProduct hp hp1 n (0 : CoeffPair p) z =
      jointDeletedSingleSpectralProduct n (z,(0 : Coeff p)) := by
  have hstd := tendsto_sourceStandardRootOmittedPartialProduct
    hp hp1 n (0 : CoeffPair p) z
  have hcrit := tendsto_jointDeletedSingleSpectralPartialProduct
    hp hp1 n (z,(0 : Coeff p))
  have hsame : (fun N => sourceStandardRootOmittedPartialProduct hp hp1 n N
      (z,(0 : CoeffPair p))) =
      fun N => jointDeletedSingleSpectralPartialProduct n N (z,(0 : Coeff p)) := by
    funext N
    exact sourceStandardRootOmittedPartialProduct_zero_source_eq_deleted
      hp hp1 n N z
  rw [hsame] at hstd
  exact tendsto_nhds_unique hstd hcrit

/-- The normalized-action extension takes the expected free value
at zero source for every spectral index. -/
theorem sourceNormalizedActionComplexExtension_zero_source
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourceNormalizedActionComplexExtension hp hp1 n (0 : CoeffPair p) = 1/4 := by
  have hgap : sourcePeriodicGapDisplacement hp hp1 (0 : CoeffPair p) n = 0 := by
    simp only [sourcePeriodicGapDisplacement_apply, map_zero]
    simp [canonicalPeriodicGap_zero]
  have hmid : sourceStandardRootMidpoint hp hp1 (0 : CoeffPair p) n =
      (Real.pi : ℂ)*n := by
    simp only [sourceStandardRootMidpoint,map_zero]
    exact canonicalPeriodicMidpoint_zero hp hp1 n
  have hcrit : canonicalCriticalDisplacement hp hp1
      (periodOnePotential (0 : CoeffPair p))
      (periodOnePotential_mem (0 : CoeffPair p)) = 0 := by
    simpa only [map_zero] using canonicalCriticalDisplacement_zero hp hp1
  have hsame := sourceStandardRootOmittedProduct_zero_source_eq_deleted
    hp hp1 n ((Real.pi : ℂ)*n)
  have hden : sourceStandardRootOmittedProduct hp hp1 n
      (0 : CoeffPair p) ((Real.pi : ℂ)*n) ≠ 0 := by
    obtain ⟨W,_,_,hWreal,hdisjoint⟩ :=
      exists_global_source_disjoint_periodicSegments hp hp1
    have hdomain : (Real.pi : ℂ)*n ∈
        sourceStandardRootOmittedDomain hp hp1 (0 : CoeffPair p) n := by
      rw [← hmid]
      intro m hmn hmem
      exact Set.disjoint_left.mp
        (hdisjoint 0 (hWreal (by simp [realTypeSourceLocus])) n m
          (Ne.symm hmn))
        (sourcePeriodicMidpoint_mem_segment hp hp1 0 n) hmem
    exact sourceStandardRootOmittedProduct_ne_zero
      hp hp1 0 ((Real.pi : ℂ)*n) n hdomain
  simp only [sourceNormalizedActionComplexExtension,
    sourceNormalizedActionRealExtension, if_pos hgap,
    sourceNormalizedActionCollapsedCandidate,
    sourceCriticalRootRatioExtension, sourceSingleRootQuotientJointProduct,
    sourceStandardRootOmittedJointProduct,
    hmid, hcrit]
  rw [← hsame]
  field_simp [hden]
  simp [Complex.I_sq]

end NLS.ZakharovShabat
