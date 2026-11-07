import NLS.KdV.HillAnglePairSpectralReality
import NLS.KdV.MiuraCanonicalRootReflection
import NLS.SequenceSpaces.OddPositiveScalarExtension
import NLS.ZakharovShabat.SourceEntireGapContourZeros
import NLS.ZakharovShabat.SourceGapSampleSummability

/-! Every actual angle-pair spectral variation has a full odd
frequency zero sequence, with one zero in each actual periodic gap.
Its displacement is in the original Hilbert sequence space. Open,
collapsed and central gaps are all included. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P Q : HillProductEquationPatch} {n m : ℕ+}

theorem completePhasePairFrequencyVariation_period_eq_zero
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (k : ℕ+) (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) :
    (∮ z in C((P.centers ((k:ℕ):ℤ):ℂ),P.radii ((k:ℕ):ℤ)),
      C.completePhasePairFrequencyVariation D q z/
        sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi q) z)=0 := by
  rw [show (∮ z in C((P.centers ((k:ℕ):ℤ):ℂ),P.radii ((k:ℕ):ℤ)),
      C.completePhasePairFrequencyVariation D q z/
        sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi q) z) =
      (∮ z in C((P.centers ((k:ℕ):ℤ):ℂ),P.radii ((k:ℕ):ℤ)),
        (z/sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi q) z)*
          C.completePhasePairDiscriminantBracket D q
            (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))) from by
    apply circleIntegral.integral_congr (P.radii_pos _).le
    intro z _
    dsimp only [completePhasePairFrequencyVariation]
    ring]
  exact C.completePhasePairDiscriminant_prescribed_period_eq_zero D k q hqC hqD hr

theorem exists_completePhasePairFrequencyVariation_zero_on_positive_gap
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (k : ℕ+) (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((k:ℕ):ℤ),
      C.completePhasePairFrequencyVariation D q z=0 := by
  have hqP := (C.subset hqC).1
  let A := P.isolating.periodCircle (P.sourcePsi q) (P.image q hqP).2 ((k:ℕ):ℤ)
    (P.centers ((k:ℕ):ℤ)) (P.radii ((k:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  let F := C.completePhasePairFrequencyVariation D q
  have hF := C.analytic_completePhasePairFrequencyVariation D q
  have hreal := P.sourcePsi_real q hqP hr
  have hperiod := C.completePhasePairFrequencyVariation_period_eq_zero D k q hqC hqD hr
  rcases sourcePeriodicGap_eq_zero_or_open (by norm_num) (by norm_num) (P.sourcePsi q) hreal ((k:ℕ):ℤ)
    with hclosed | hopen
  · have hmid := sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((k:ℕ):ℤ)
    exact ⟨_,hmid,sourceEntireNumerator_zero_at_collapsedGap (by norm_num) (by norm_num)
      (P.sourcePsi q) hreal ((k:ℕ):ℤ) F hF hclosed _ _ (P.radii_pos _)
      (A.gap hmid) A.closedBall_subset_omittedDomain A.sphere_subset_rootDomain hperiod⟩
  · obtain ⟨z,hz,hzero⟩ := exists_sourceEntireNumerator_zero_on_openGap (by norm_num) (by norm_num)
      (P.sourcePsi q) hreal ((k:ℕ):ℤ) F hF
      (C.completePhasePairFrequencyVariation_im_eq_zero_of_real D q hqC hqD hr) hopen
      (P.centers ((k:ℕ):ℤ)) (P.radii ((k:ℕ):ℤ)) (P.radii_pos _) A.gap
      A.closedBall_subset_omittedDomain A.sphere_subset_rootDomain hperiod
    exact ⟨z,sourceStandardRoot_gapSegment_subset_periodicSegment (by norm_num) (by norm_num)
      (P.sourcePsi q) ((k:ℕ):ℤ) hz,hzero⟩

theorem exists_completePhasePairFrequencyVariation_odd_gapZero_sequence
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ ρ : ℤ → ℂ, (∀ j : ℤ, ρ (-j) = -ρ j) ∧ ρ 0=0 ∧
      Memℓp (fun j => ρ j-(Real.pi:ℂ)*j) 2 ∧
      ∀ j : ℤ, ρ j ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) j ∧
        C.completePhasePairFrequencyVariation D q (ρ j)=0 := by
  classical
  choose a ha hz using (fun k : ℕ+ => C.exists_completePhasePairFrequencyVariation_zero_on_positive_gap D k q hqC hqD hr)
  let ρ := oddPositiveScalarExtension a
  let hreflection := sourcePeriodicReflection_hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift q)
  have hρpos (k : ℕ+) : ρ ((k:ℕ):ℤ)=a k := oddPositiveScalarExtension_apply a k
  have hρneg (j : ℤ) : ρ (-j) = -ρ j := oddPositiveScalarExtension_neg a j
  have hρ0 : ρ 0=0 := oddPositiveScalarExtension_zero a
  have hall (j : ℤ) : ρ j ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) j ∧
      C.completePhasePairFrequencyVariation D q (ρ j)=0 := by
    by_cases hj : j=0
    · subst j
      rw [hρ0]
      have hs := sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) 0
      have hmid : sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) 0=0 := by
        have he := (hreflection 0).1
        simp only [neg_zero] at he
        dsimp only [sourceStandardRootMidpoint,canonicalPeriodicMidpoint,HillProductEquationPatch.sourcePsi]
        rw [he]
        ring
      refine ⟨by simpa only [hmid] using hs,?_⟩
      simp only [completePhasePairFrequencyVariation,zero_mul]
    · by_cases hp : 0<j
      · let k : ℕ+ := ⟨j.toNat,by omega⟩
        have he : ((k:ℕ):ℤ)=j := by change (j.toNat:ℤ)=j; omega
        rw [← he,hρpos]
        exact ⟨ha k,hz k⟩
      · let k : ℕ+ := ⟨(-j).toNat,by omega⟩
        have he : j = -((k:ℕ):ℤ) := by change j = -(((-j).toNat:ℕ):ℤ); omega
        rw [he,hρneg,hρpos]
        exact ⟨(hreflection.neg_mem_segment_iff ((k:ℕ):ℤ) (a k)).mpr (ha k),by
          rw [C.completePhasePairFrequencyVariation_neg D q (a k),hz k,neg_zero]⟩
  exact ⟨ρ,hρneg,hρ0,memℓp_sourcePeriodicSegment_samples (by norm_num) (by norm_num)
    (P.sourcePsi q) ρ (fun j => (hall j).1),hall⟩

end NLS.KdV.HillPhysicalOnIndexPhaseChart
