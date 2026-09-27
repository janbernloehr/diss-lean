import NLS.ZakharovShabat.SourceNormalizedActionCollapsedNonzero
import NLS.ZakharovShabat.SourceStandardRootOmittedRealGap
import NLS.ZakharovShabat.RealDeletedPeriodicProduct

/-!
# Reality of the normalized action at collapsed real gaps

The deleted standard-root product is real at every real spectral
point avoiding the retained gap segments, even when the selected gap
has collapsed. The deleted critical product is real whenever its
root sequence and spectral argument are real. These facts identify
the collapsed normalized-action value as a real number.
-/

noncomputable section
open Set Complex ComplexConjugate Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every retained standard-root factor is real at a real point of
the omitted-product domain. -/
theorem sourceStandardRoot_im_eq_zero_on_omittedDomain_realAxis
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (x : ℝ)
    (hx : (x:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (sourceStandardRoot hp hp1 ψ m (x:ℂ)).im = 0 := by
  have hnot : x ∉ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re := by
    intro hmem
    exact hx m hmn
      (sourcePeriodicSegment_mem_of_realIcc hp hp1 ψ hreal m x hmem)
  have hside : x < (canonicalPeriodicLeft hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m).re ∨
      (canonicalPeriodicRight hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) m).re < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hnot
  exact sourceStandardRoot_im_eq_zero_of_real_exterior
    hp hp1 ψ hreal m x hside

/-- Finite omitted standard-root products are real at real points of
their moving-gap complement. -/
theorem sourceStandardRootOmittedPartialProduct_im_eq_zero_on_realAxis
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (N : ℕ) (x : ℝ)
    (hx : (x:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (sourceStandardRootOmittedPartialProduct hp hp1 n N ((x:ℂ),ψ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have hden (m : ℤ) : conj (singleSpectralDenominator m) =
      singleSpectralDenominator m := by
    unfold singleSpectralDenominator
    split_ifs <;> simp
  have hfactor (m : ℤ) (hm : m ≠ n) :
      conj (sourceStandardRoot hp hp1 ψ m (x:ℂ) /
        singleSpectralDenominator m) =
      sourceStandardRoot hp hp1 ψ m (x:ℂ) /
        singleSpectralDenominator m := by
    rw [map_div₀, hden]
    rw [Complex.conj_eq_iff_im.mpr
      (sourceStandardRoot_im_eq_zero_on_omittedDomain_realAxis
        hp hp1 ψ hreal n m hm x hx)]
  unfold sourceStandardRootOmittedPartialProduct
  rw [map_div₀, map_prod, hden]
  congr 1
  apply Finset.prod_congr rfl
  intro m hm
  exact hfactor m (Finset.mem_erase.mp hm).1

/-- The infinite omitted standard-root product is real throughout
its real-axis domain for real-type sources. -/
theorem sourceStandardRootOmittedProduct_im_eq_zero_on_realAxis
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (x : ℝ)
    (hx : (x:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (sourceStandardRootOmittedProduct hp hp1 n ψ (x:ℂ)).im = 0 := by
  have ht := tendsto_sourceStandardRootOmittedPartialProduct
    hp hp1 n ψ (x:ℂ)
  have hc := continuous_conj.continuousAt.tendsto.comp ht
  have heq (N : ℕ) :
      conj (sourceStandardRootOmittedPartialProduct hp hp1 n N ((x:ℂ),ψ)) =
        sourceStandardRootOmittedPartialProduct hp hp1 n N ((x:ℂ),ψ) :=
    Complex.conj_eq_iff_im.mpr
      (sourceStandardRootOmittedPartialProduct_im_eq_zero_on_realAxis
        hp hp1 ψ hreal n N x hx)
  simp only [Function.comp_def] at hc
  simp_rw [heq] at hc
  exact Complex.conj_eq_iff_im.mp (tendsto_nhds_unique hc ht)

/-- A finite deleted critical product is real at a real spectral
argument if all critical roots are real. -/
theorem jointDeletedSingleSpectralPartialProduct_im_eq_zero_of_real_roots
    (n : ℤ) (N : ℕ) (a : Coeff p) (x : ℝ)
    (hroots : ∀ m : ℤ, (displacedRoots a m).im = 0) :
    (jointDeletedSingleSpectralPartialProduct n N ((x:ℂ),a)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have hden (m : ℤ) : conj (singleSpectralDenominator m) =
      singleSpectralDenominator m := by
    unfold singleSpectralDenominator
    split_ifs <;> simp
  have hfactor (m : ℤ) :
      conj (singleSpectralFactor (displacedRoots a) (x:ℂ) m) =
        singleSpectralFactor (displacedRoots a) (x:ℂ) m := by
    unfold singleSpectralFactor
    rw [map_div₀, map_sub, hden]
    rw [Complex.conj_eq_iff_im.mpr (hroots m)]
    simp
  unfold jointDeletedSingleSpectralPartialProduct
  rw [map_div₀, map_prod, hden]
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  exact hfactor m

/-- The deleted critical product is real on the real axis if its
critical-root sequence is real. -/
theorem jointDeletedSingleSpectralProduct_im_eq_zero_of_real_roots
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (x : ℝ)
    (hroots : ∀ m : ℤ, (displacedRoots a m).im = 0) :
    (jointDeletedSingleSpectralProduct n ((x:ℂ),a)).im = 0 := by
  have ht := tendsto_jointDeletedSingleSpectralPartialProduct
    hp hp1 n ((x:ℂ),a)
  have hc := continuous_conj.continuousAt.tendsto.comp ht
  have heq (N : ℕ) :
      conj (jointDeletedSingleSpectralPartialProduct n N ((x:ℂ),a)) =
        jointDeletedSingleSpectralPartialProduct n N ((x:ℂ),a) :=
    Complex.conj_eq_iff_im.mpr
      (jointDeletedSingleSpectralPartialProduct_im_eq_zero_of_real_roots
        n N a x hroots)
  simp only [Function.comp_def] at hc
  simp_rw [heq] at hc
  exact Complex.conj_eq_iff_im.mp (tendsto_nhds_unique hc ht)

/-- The normalized-action extension has zero imaginary part at a
collapsed real-type periodic gap. -/
theorem sourceNormalizedActionComplexExtension_im_eq_zero_of_realType_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) :
    (sourceNormalizedActionComplexExtension hp hp1 n ψ).im = 0 := by
  let a := canonicalCriticalDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  have hτim : τ.im = 0 := by
    have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType
      hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) n
    simp only [τ,canonicalPeriodicMidpoint,
      Complex.div_im,Complex.add_im,hends.1,hends.2]
    norm_num
  have hτ : ((τ.re:ℝ):ℂ) = τ := by
    apply Complex.ext
    · rfl
    · exact hτim.symm
  have hroots (m : ℤ) : (displacedRoots a m).im = 0 := by
    have heq : displacedRoots a m = canonicalCriticalPoints hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
      simp only [a,displacedRoots,canonicalCriticalDisplacement_apply]
      ring
    rw [heq]
    exact canonicalCriticalPoints_im_eq_zero hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) m
  have hnum : (jointDeletedSingleSpectralProduct n (τ,a)).im = 0 := by
    rw [← hτ]
    exact jointDeletedSingleSpectralProduct_im_eq_zero_of_real_roots
      hp hp1 n a τ.re hroots
  have hdomain : τ ∈ sourceStandardRootOmittedDomain hp hp1 ψ n := by
    obtain ⟨W,_,_,hWreal,hdisjoint⟩ :=
      exists_global_source_disjoint_periodicSegments hp hp1
    intro m hmn hmem
    exact Set.disjoint_left.mp (hdisjoint ψ (hWreal hreal) n m (Ne.symm hmn))
      (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n) hmem
  have hden : (sourceStandardRootOmittedProduct hp hp1 n ψ τ).im = 0 := by
    rw [← hτ]
    exact sourceStandardRootOmittedProduct_im_eq_zero_on_realAxis
      hp hp1 ψ hreal n τ.re (hτ ▸ hdomain)
  simp only [sourceNormalizedActionComplexExtension,
    sourceNormalizedActionRealExtension, if_pos hgap,
    sourceNormalizedActionCollapsedCandidate]
  change (I * (-I * (jointDeletedSingleSpectralProduct n (τ,a) /
    sourceStandardRootOmittedProduct hp hp1 n ψ τ)) / 4).im = 0
  have hcoef : I * (-I * (jointDeletedSingleSpectralProduct n (τ,a) /
      sourceStandardRootOmittedProduct hp hp1 n ψ τ)) / 4 =
      (jointDeletedSingleSpectralProduct n (τ,a) /
        sourceStandardRootOmittedProduct hp hp1 n ψ τ) / 4 := by
    calc
      _ = -(I^2) * (jointDeletedSingleSpectralProduct n (τ,a) /
          sourceStandardRootOmittedProduct hp hp1 n ψ τ) / 4 := by ring
      _ = _ := by simp [Complex.I_sq]
  rw [hcoef]
  simp [Complex.div_im,hnum,hden]

/-- The normalized action is real on the whole real-type locus,
including both open and collapsed periodic gaps. -/
theorem sourceNormalizedActionComplexExtension_im_eq_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    (sourceNormalizedActionComplexExtension hp hp1 n ψ).im = 0 := by
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · exact sourceNormalizedActionComplexExtension_im_eq_zero_of_realType_zeroGap
      hp hp1 n ψ hreal hgap
  · simpa only [sourceNormalizedActionComplexExtension,
      sourceNormalizedActionRealExtension, if_neg hgap] using
      sourceRawNormalizedAction_im_eq_zero_of_realType hp hp1 n ψ hreal

end NLS.ZakharovShabat
