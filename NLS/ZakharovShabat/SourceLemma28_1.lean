import NLS.ZakharovShabat.SourceCriticalFactorSmallTail
import NLS.ZakharovShabat.SourceGapFactorParameterContinuity
import NLS.ZakharovShabat.SourceRealGapFactorMargin
import NLS.ZakharovShabat.SourceProposition28_2

/-! # The complex gap-factor bound of Lemma 28.1

The printed constant is recovered independently of the false intermediate
ratio. A common connected L²-open neighborhood works for every M₁ weight.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A unit perturbation from the projected real gap preserves the printed constant. -/
theorem sourceM1_gapFactorValue_le_of_realPart_bound
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : CoeffPair 2) (n : ℤ)
    (hn : 8*‖a‖^2 ≤ 1+|(n:ℝ)|) (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1)
    (hd : ‖sourceGapFactorValue n (normalizedWeightedSource w a) t-
      sourceGapFactorValue n (sourceRealPart (normalizedWeightedSource w a)) t‖ ≤ 1) :
    ‖sourceGapFactorValue n (normalizedWeightedSource w a) t‖ ≤ 2048*(1+‖a‖^2) := by
  let b : realTypeSourceSubmodule 2 := ⟨sourceRealPart a,sourceRealPart_realType a⟩
  have hsq := pow_le_pow_left₀ (norm_nonneg (sourceRealPart a)) (norm_sourceRealPart_le (by simp) a) 2
  have hb := sourceM1_real_gapFactor_le_1024_normalized w hw b n
    (by change 8*‖sourceRealPart a‖^2 ≤ 1+|(n:ℝ)|; linarith)
  have hp := (sourceRealGapFactor (by simp) (by norm_num) (normalizedWeightedSource w b.val)
    (normalizedWeightedSource_realType w b.val b.property) n).norm_coe_le_norm ⟨t,ht⟩
  have hr := hp.trans hb
  change ‖sourceGapFactorValue n (normalizedWeightedSource w (sourceRealPart a)) t‖ ≤
    1024*(1+‖sourceRealPart a‖^2) at hr
  rw [normalizedWeightedSource_sourceRealPart] at hr
  have he := norm_add_le
    (sourceGapFactorValue n (normalizedWeightedSource w a) t-
      sourceGapFactorValue n (sourceRealPart (normalizedWeightedSource w a)) t)
    (sourceGapFactorValue n (sourceRealPart (normalizedWeightedSource w a)) t)
  rw [sub_add_cancel] at he
  linarith [sq_nonneg ‖a‖]

/-- Uniform distant control and a finite intersection of compact-gap comparisons
produce the local complex estimate in the original L² topology. -/
theorem exists_local_sourceM1_gapFactor_bound (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ ∈ U ∧
      ∀ w : SpectralWeight, w.HasLinearFactor → ∀ a : CoeffPair 2,
        normalizedWeightedSource w a ∈ U → ∀ n : ℤ, 8*‖a‖^2 ≤ 1+|(n:ℝ)| →
          ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (normalizedWeightedSource w a) n,
            ‖sourceCriticalRootRatioExtension (by simp) (by norm_num) n (normalizedWeightedSource w a) z‖ ≤
              2048*(1+‖a‖^2) := by
  classical
  obtain ⟨V,hV,hφV,K,htail⟩ := exists_local_sourceCriticalFactor_tail_le_three φ hφ
  have hlocal (n : ℤ) := exists_local_sourceGapFactor_realPart_comparison φ hφ n
  choose O hO hφO hhead using hlocal
  let S := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let H := ⋂ n ∈ S, O n
  have hH : IsOpen H := isOpen_biInter_finset (fun n _ => hO n)
  have hφH : φ ∈ H := by simp only [H,mem_iInter]; exact fun n _ => hφO n
  refine ⟨V ∩ H,hV.inter hH,⟨hφV,hφH⟩,?_⟩
  intro w hw a ha n hn z hz
  by_cases hK : K ≤ n.natAbs
  · exact (htail _ ha.1 n hK z hz).trans (by nlinarith [sq_nonneg ‖a‖])
  · have hnS : n ∈ S := by simp only [S,Finset.mem_Icc]; omega
    have hOa : normalizedWeightedSource w a ∈ O n := mem_iInter.mp (mem_iInter.mp ha.2 n) hnS
    rw [← sourceStandardRoot_gapSegment_eq_periodicSegment] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    have hb := sourceM1_gapFactorValue_le_of_realPart_bound w hw a n hn t ht
      (hhead n _ hOa t ht)
    simpa only [sourceGapFactorValue,sourceCanonicalRootGapPoint,norm_mul,norm_I,one_mul] using hb

/-- The complete scalar bound of Lemma 28.1 on a connected L²-open neighborhood.
Its choice precedes all weights, potentials, indices, and points of each complex gap. -/
theorem exists_sourceM1_gapFactor_neighborhood :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
      U ⊆ sourceSpectralStripNeighborhood (by simp) ∧
      ∀ w : SpectralWeight, w.HasLinearFactor → ∀ a : CoeffPair 2,
        normalizedWeightedSource w a ∈ U → ∀ n : ℤ, 8*‖a‖^2 ≤ 1+|(n:ℝ)| →
          ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (normalizedWeightedSource w a) n,
            ‖sourceCriticalRootRatioExtension (by simp) (by norm_num) n (normalizedWeightedSource w a) z‖ ≤
              2048*(1+‖a‖^2) := by
  classical
  have hlocal (φ : realTypeSourceSubmodule 2) := exists_local_sourceM1_gapFactor_bound φ.val φ.property
  choose V hV hφV hb using hlocal
  let S : Set (CoeffPair 2) := (⋃ φ : realTypeSourceSubmodule 2, V φ) ∩
    sourceSpectralStripNeighborhood (by simp)
  have hS : IsOpen S := (isOpen_iUnion hV).inter (isOpen_sourceSpectralStripNeighborhood (by simp))
  have hrealS : realTypeSourceLocus 2 ⊆ S := fun φ hφ =>
    ⟨mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφV ⟨φ,hφ⟩⟩,
      real_mem_sourceSpectralStripNeighborhood (by simp) (by norm_num) φ hφ⟩
  let U := connectedComponentIn S (0 : CoeffPair 2)
  have hzero : (0 : CoeffPair 2) ∈ realTypeSourceLocus 2 := by simp [realTypeSourceLocus]
  have hrealU : realTypeSourceLocus 2 ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  refine ⟨U,hS.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),
    hrealU,fun ψ hψ => (hUS hψ).2,?_⟩
  intro w hw a ha n hn z hz
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS ha).1
  exact hb φ w hw a hφ n hn z hz

/-- The physical H¹ formulation of Lemma 28.1, including equality at the cutoff
and the entire closed gap. The false intermediate ratio is not asserted. -/
theorem exists_sourceH1_lemma28_1 :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
      U ⊆ sourceSpectralStripNeighborhood (by simp) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2, sobolevSourceInclusion a ∈ U →
        ∀ n : ℤ, 8*‖sourcePhysicalH1Coordinates a‖^2 ≤ 1+|(n:ℝ)| →
          ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (sobolevSourceInclusion a) n,
            ‖sourceCriticalRootRatioExtension (by simp) (by norm_num) n (sobolevSourceInclusion a) z‖ ≤
              2048*(1+‖sourcePhysicalH1Coordinates a‖^2) := by
  obtain ⟨U,hU,hc,hr,hs,hb⟩ := exists_sourceM1_gapFactor_neighborhood
  refine ⟨U,hU,hc,hr,hs,?_⟩
  intro a ha n hn z hz
  have h := hb (SpectralWeight.piSobolev 1 (by norm_num))
    (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl) (sourcePhysicalH1Coordinates a)
    (by simpa only [normalizedWeightedSource_physicalH1Coordinates] using ha) n hn z
    (by simpa only [normalizedWeightedSource_physicalH1Coordinates] using hz)
  simpa only [normalizedWeightedSource_physicalH1Coordinates] using h

/-- The two Section 28 estimates hold on the same connected L²-open neighborhood
of the whole real locus, with their respective printed index thresholds. -/
theorem exists_sourceH1_section28_estimates :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
      U ⊆ sourceSpectralStripNeighborhood (by simp) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2, sobolevSourceInclusion a ∈ U →
        (∀ n : ℤ, 8*‖sourcePhysicalH1Coordinates a‖^2 ≤ 1+|(n:ℝ)| →
          ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (sobolevSourceInclusion a) n,
            ‖sourceCriticalRootRatioExtension (by simp) (by norm_num) n (sobolevSourceInclusion a) z‖ ≤
              2048*(1+‖sourcePhysicalH1Coordinates a‖^2)) ∧
        (∀ n : ℤ, 8*‖sourcePhysicalH1Coordinates a‖^2 ≤ |(n:ℝ)| →
          ‖sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a)‖ ≤
            4608*(1+‖sourcePhysicalH1Coordinates a‖^2)*
              ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a) n‖^2) := by
  obtain ⟨V,hV,_,hrV,hsV,hgap⟩ := exists_sourceH1_lemma28_1
  obtain ⟨W,hW,_,hrW,_,haction⟩ := exists_sourceH1_proposition28_2
  let S := V ∩ W
  have hS : IsOpen S := hV.inter hW
  have hrS : realTypeSourceLocus 2 ⊆ S := fun ψ hψ => ⟨hrV hψ,hrW hψ⟩
  have hz : (0 : CoeffPair 2) ∈ realTypeSourceLocus 2 := by simp [realTypeSourceLocus]
  let U := connectedComponentIn S (0 : CoeffPair 2)
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  refine ⟨U,hS.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr (hrS hz),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hz hrS,
    fun ψ hψ => hsV (hUS hψ).1,?_⟩
  intro a ha
  exact ⟨hgap a (hUS ha).1,haction a (hUS ha).2⟩

end NLS.ZakharovShabat
