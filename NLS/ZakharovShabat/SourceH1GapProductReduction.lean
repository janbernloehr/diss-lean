import NLS.ZakharovShabat.SourceH1ExteriorProductBound
import NLS.ComplexAnalysis.FiniteCoreProductBound
import NLS.ZakharovShabat.SourceRealGapFactorBound

/-! # Reducing Lemma 28.1's actual infinite product to its finite central part

The limiting product is the existing deleted critical-root quotient. No
new infinite-product candidate is introduced, and no central factor is
assumed nonzero. At cutoff zero the central part is empty, yielding a
complete bound on the entire gap for small H¹ sources.
-/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any finite exterior-product bound transfers to the actual deleted
critical-root quotient, retaining the central factors multiplicatively. -/
theorem sourceCriticalRootRatioExtension_le_finite_core
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (N : ℕ)
    (hn : N ≤ n.natAbs) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) (C : ℝ)
    (hbound : ∀ s : Finset ℤ, n ∉ s → (∀ m ∈ s, N ≤ m.natAbs) →
      ‖∏ m ∈ s, (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
        sourceStandardRoot hp hp1 ψ m z‖ ≤ C) :
    ‖sourceCriticalRootRatioExtension hp hp1 n ψ z‖ ≤
      C*‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ),
        (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
          sourceStandardRoot hp hp1 ψ m z‖ := by
  let a := canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hseq : displacedRoots a = canonicalCriticalPoints hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) := by
    funext m
    simp only [a,displacedRoots,canonicalCriticalDisplacement_apply]
    ring
  have hlim := tendsto_sourceSingleRootQuotientPartialProduct hp hp1 n Set.univ
    (z,(a,ψ)) ⟨Set.mem_univ _,hz⟩
  simp only [sourceSingleRootQuotientPartialProduct,hseq] at hlim
  have h := NLS.ComplexAnalysis.norm_symmetric_product_limit_le_core _ n N hn _ C hlim hbound
  simpa only [sourceCriticalRootRatioExtension,norm_mul,norm_neg,Complex.norm_I,one_mul] using h

/-- The full real-source product is bounded by 128 times its finite central part. -/
theorem sourceH1_real_gap_product_le_128_core (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ.val n) :
    ‖sourceCriticalRootRatioExtension (by simp) (by norm_num) n ψ.val z‖ ≤
      128*‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ),
        (canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential ψ.val)
          (periodOnePotential_mem ψ.val) m-z)/sourceStandardRoot (by simp) (by norm_num) ψ.val m z‖ := by
  have hdom := sourceStandardRootGapSegment_subset_omittedDomain_of_realType
    (by simp) (by norm_num) ψ.val ψ.property n
  rw [sourceStandardRoot_gapSegment_eq_periodicSegment] at hdom
  apply sourceCriticalRootRatioExtension_le_finite_core (by simp) (by norm_num)
    ψ.val n N hn z (hdom hz) 128
  intro s hs hsext
  exact sourceH1_real_exterior_product_le_128 ψ φ hφ N hN s n hs hsext hn z hz

/-- If the H¹ norm permits cutoff zero, the full closed-gap factor is bounded by 128. -/
theorem sourceH1_real_gapFactor_le_128_of_small_norm (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (hsmall : 8*‖φ‖^2 ≤ 1) (n : ℤ) :
    ‖sourceRealGapFactor (by simp) (by norm_num) ψ.val ψ.property n‖ ≤ 128 := by
  apply (sourceRealGapFactor_norm_le_iff (by simp) (by norm_num)
    ψ.val ψ.property n 128 (by norm_num)).mpr
  intro z hz
  have h := sourceH1_real_gap_product_le_128_core ψ φ hφ 0 (by simpa using hsmall)
    n (Nat.zero_le _) z hz
  simpa only [Nat.cast_zero,neg_zero,Finset.Ioo_self,Finset.prod_empty,norm_one,mul_one] using h

/-- The small-H¹ regime yields a complete action-gap bound at every index,
including collapsed gaps, with the real-source factor three. -/
theorem sourceH1_real_action_le_96_gap_sq_of_small_norm (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (hsmall : 8*‖φ‖^2 ≤ 1) (n : ℤ) :
    ‖sourceComplexAction (by simp) (by norm_num) n ψ.val‖ ≤
      96*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ.val n‖^2 := by
  have h := sourceComplexAction_le_three_gapFactor_mul_gap_sq
    (by simp) (by norm_num) ψ.val ψ.property n
  have hfactor := sourceH1_real_gapFactor_le_128_of_small_norm ψ φ hφ hsmall n
  have hmul := mul_le_mul_of_nonneg_right hfactor
    (sq_nonneg ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ.val n‖)
  nlinarith

end NLS.ZakharovShabat
