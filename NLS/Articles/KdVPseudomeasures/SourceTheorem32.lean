import NLS.Articles.KdVPseudomeasures.OriginalCanonicalActionQuotients
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeCartesianMap
import NLS.KdV.HillNativeRealSignedMap
import NLS.KdV.HillSignedEndpointBound

/-! All three assertions of Theorem 3.2 on one actual complex mean-zero
Birkhoff neighborhood. The raw quotient is defined where the gap square
is nonzero; the printed Z_n/complement is reversed. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

private theorem source32_native_subset_ratio :
    hillHminusActionAngleNativeDomain ⊆ hillHminusCanonicalRatioDomain :=
  fun _ h => hillHminusActionAmplitudeDomain_subset_ratio
    (hillHminusActionAngleEnergyDomain_subset (hillHminusActionAngleNativeDomain_subset h)).1

private theorem source32_coordinate (q : HillMeanZeroSource) (k : ℤ) :
    (hillMeanZeroComplexMap q).val.val k=(hillHminusNativeComplexMap q.val).val k :=
  congrArg (fun z : WeightedCoeff (Weight.signedSobolev (-1/2)) 2 => z.val k)
    (hillMeanZeroComplexMap_coe q)

private theorem source32_signed_local_bound (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAngleNativeDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖(hillHminusNativeComplexMap a).val (n:ℤ)‖ ≤
          (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n a ∧
        ‖(hillHminusNativeComplexMap a).val (-(n:ℤ))‖ ≤
          (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n a := by
  obtain ⟨V,hV,hqV,_,C,hC,hb⟩ := exists_locally_uniform_actionAngle_original_energy_bound q
    (hillHminusActionAngleNativeDomain_subset hq)
  refine ⟨V ∩ hillHminusActionAngleNativeDomain,hV.inter isOpen_hillHminusActionAngleNativeDomain,
    ⟨hqV,hq⟩,inter_subset_right,C,hC,?_⟩
  intro a ha n
  have h := hb a ha.1 n
  constructor
  · rw [hillHminusNativeComplexMap_positive a ha.2 n]
    exact (norm_div_sqrt_two_le _).trans h.2.1
  · rw [hillHminusNativeComplexMap_negative a ha.2 n]
    exact (norm_div_sqrt_two_le _).trans h.1

/-- The complete source assertions. The canonical squared gap is used to
express the ordering-independent complex gap and its zero locus. -/
theorem sourceTheorem3_2 :
    ∃ W : Set HillMeanZeroSource, IsOpen W ∧
      (∀ q : HillRealMeanZeroSource, q.val ∈ W) ∧
      AnalyticOnNhd ℂ hillMeanZeroComplexMap W ∧
      hillMeanZeroComplexMap 0=0 ∧
      (∀ n : ℕ+,
        AnalyticOnNhd ℂ (fun q : HillMeanZeroSource => hillHminusCanonicalActionQuotient n q.val) W ∧
        ∀ q ∈ W,
          (hillMeanZeroComplexMap q).val.val (n:ℤ)*(hillMeanZeroComplexMap q).val.val (-(n:ℤ))=
            hillHminusCanonicalAction n q.val ∧
          (hillHminusCanonicalAction n q.val=0 ↔ hillHminusCanonicalGapSquare n q.val=0) ∧
          (hillHminusCanonicalGapSquare n q.val ≠ 0 →
            hillHminusCanonicalActionQuotient n q.val=
              hillHminusCanonicalAction n q.val/hillHminusCanonicalGapSquare n q.val)) ∧
      (∀ q ∈ W, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∃ U : Set HillMeanZeroSource, 2 ≤ N ∧ IsOpen U ∧ q ∈ U ∧ U ⊆ W ∧
          ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ a ∈ U,
            ‖(8*((Real.pi:ℂ)*(n:ℕ)))*hillHminusCanonicalActionQuotient n a.val-1‖ ≤ epsilon) ∧
      ∀ q ∈ W, ∃ U : Set HillMeanZeroSource, IsOpen U ∧ q ∈ U ∧ U ⊆ W ∧
        ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
          ‖(hillMeanZeroComplexMap a).val.val (n:ℤ)‖ ≤
            (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n a.val ∧
          ‖(hillMeanZeroComplexMap a).val.val (-(n:ℤ))‖ ≤
            (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n a.val := by
  let L := (zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL
  refine ⟨hillMeanZeroComplexDomain,isOpen_hillMeanZeroComplexDomain,
    (fun q => real_mem_hillMeanZeroComplexDomain q.val q.property),
    analyticOnNhd_hillMeanZeroComplexMap,hillMeanZeroComplexMap_zero,?_,?_,?_⟩
  · intro n
    constructor
    · intro q hq
      exact (analyticOnNhd_hillHminusCanonicalActionQuotient n q.val
        (source32_native_subset_ratio hq)).comp (L.analyticAt q)
    · intro q hq
      have hr := source32_native_subset_ratio hq
      refine ⟨?_,hillHminusCanonicalAction_eq_zero_iff_gapSquare n q.val hr,
        hillHminusCanonicalActionQuotient_eq_raw n q.val hr⟩
      exact (congrArg₂ (fun x y : ℂ => x*y) (source32_coordinate q (n:ℤ))
        (source32_coordinate q (-(n:ℤ)))).trans
        (hillHminusNativeComplexMap_action_identity q.val hq n)
  · intro q hq epsilon he
    obtain ⟨N,V,hN,hV,hqV,_,hb⟩ := exists_hillHminusCanonicalActionQuotient_uniform_high q.val
      (source32_native_subset_ratio hq) epsilon he
    let U := hillMeanZeroComplexDomain ∩ L ⁻¹' V
    refine ⟨N,U,hN,isOpen_hillMeanZeroComplexDomain.inter (hV.preimage L.continuous),
      ⟨hq,hqV⟩,inter_subset_left,?_⟩
    intro n hn a ha
    exact hb n hn a.val ha.2
  · intro q hq
    obtain ⟨V,hV,hqV,_,C,hC,hb⟩ := source32_signed_local_bound q.val hq
    let U := hillMeanZeroComplexDomain ∩ L ⁻¹' V
    refine ⟨U,isOpen_hillMeanZeroComplexDomain.inter (hV.preimage L.continuous),
      ⟨hq,hqV⟩,inter_subset_left,C,hC,?_⟩
    intro a ha n
    have h := hb a.val ha.2 n
    exact ⟨(congrArg norm (source32_coordinate a (n:ℤ))).le.trans h.1,
      (congrArg norm (source32_coordinate a (-(n:ℤ)))).le.trans h.2⟩

end NLS.Articles.KdVPseudomeasures
