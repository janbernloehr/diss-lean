import NLS.KdV.HillAbelianFilledQuotient

/-! The endpoint-normalized OFF-INDEX family is jointly analytic on
the WHOLE original complex cut-disc domain, with the SAME source
patch before ALL n,m. Its filled quadratic quotient is analytic even
ON the cut, including every complex collapsed pair. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def offIndexAbelianJointDomain (P : HillProductEquationPatch) (m : ℕ+) : Set (ℂ × PeriodOneHminusOne) :=
  (ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source) ∩ P.abelianJointFrequencyDomain

theorem offIndexAbelianJointDomain_open (P : HillProductEquationPatch) (m : ℕ+) : IsOpen (P.offIndexAbelianJointDomain m) :=
  (isOpen_ball.prod P.source_open).inter P.abelianJointFrequencyDomain_open

theorem offIndexAbelianJointDomain_mem_iff (P : HillProductEquationPatch) (m : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : t ∈ P.offIndexAbelianJointDomain m ↔ t.2 ∈ P.source ∧ t.1 ∈ P.abelianGapDisc m t.2 := by
  constructor
  · intro ht
    exact ⟨ht.1.2,ht.1.1,ht.2.2 _⟩
  · intro ht
    let D := P.isolating.periodCircle (P.sourcePsi t.2) (P.image t.2 ht.1).2 ((m:ℕ):ℤ)
      (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
    refine ⟨⟨ht.2.1,ht.1⟩,ht.1,?_⟩
    intro j
    by_cases hj : j = ((m:ℕ):ℤ)
    · subst j; exact ht.2.2
    · exact D.closedBall_subset_omittedDomain (ball_subset_closedBall ht.2.1) j hj

def offIndexAbelianNormalizedPrimitive (P : HillProductEquationPatch) (n m : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1*P.offIndexAbelianFilledQuotient n m t

theorem analytic_offIndexAbelianNormalizedPrimitive (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ (P.offIndexAbelianNormalizedPrimitive n m) (P.offIndexAbelianJointDomain m) := by
  intro t ht
  exact (P.analytic_abelianSelectedRoot m t ⟨ht.1.2,ht.2.2 _⟩).mul
    (P.analytic_offIndexAbelianFilledQuotient n m hmn t ht.1)

theorem hasDerivAt_offIndexAbelianNormalizedPrimitive (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ) (hz : z ∈ P.abelianGapDisc m q) :
    HasDerivAt (fun w => P.offIndexAbelianNormalizedPrimitive n m (w,q)) (P.abelianFrequencyDifferential n (z,q)) z := by
  let Q := sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)
  let H : ℂ → ℂ := fun w => P.offIndexAbelianFilledQuotient n m (w,q)
  have hH : AnalyticAt ℂ H z := (P.analytic_offIndexAbelianFilledQuotient n m hmn (z,q) ⟨hz.1,hq⟩).comp
    (f := fun t : ℂ => (t,q)) (analyticAt_id.prod analyticAt_const)
  have hsq : (fun w => Q w^2) =ᶠ[𝓝 z] sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) := by
    filter_upwards [(P.abelianGapDisc_open m q).mem_nhds hz] with w hw
    exact (sourceStandardRoot_sq_of_not_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w hw.2).trans
      (sourceAngularSelectedPolynomial_eq_endpoint_factor (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w).symm
  have hd := hasDerivAt_root_mul_of_quadratic_equation Q H
    (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))
    ((canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))^2/4)
    (P.abelianGapNumerator n m (z,q)) z (sourceStandardRoot_analyticAt (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z hz.2)
    (sourceStandardRoot_ne_zero_off_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z hz.2) hsq hH
    (P.offIndexAbelianFilledQuotient_equation n m hmn q hq z hz.1)
  have hroot := ((P.offIndexAbelianJointDomain_mem_iff m (z,q)).mpr ⟨hq,hz⟩).2.2
  rw [P.abelianFrequencyDifferential_eq_gap_quotient n m (z,q) hroot]
  exact hd

theorem offIndexAbelianNormalizedPrimitive_endpoint_limit (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ),
      canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ)} : Set ℂ)) :
    Tendsto (fun z => P.offIndexAbelianNormalizedPrimitive n m (z,q)) (𝓝[P.abelianGapDisc m q] a) (𝓝 0) := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have haB : a ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) := by
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with h | h
    · rw [h]; exact D.gap (left_mem_segment ℝ _ _)
    · rw [h]; exact D.gap (right_mem_segment ℝ _ _)
  have hpoly := (hasDerivAt_quadraticRootPolynomial
    (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))
    ((canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))^2/4) a).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := P.abelianGapDisc m q))
  have hzero : sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) a = 0 := by
    rw [sourceAngularSelectedPolynomial_eq_endpoint_factor]
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with h | h <;> rw [h] <;> simp
  change Tendsto (sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))
    (𝓝[P.abelianGapDisc m q] a) (𝓝 (sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) a)) at hpoly
  rw [hzero] at hpoly
  have hs : Tendsto (fun z => (sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z)^2)
      (𝓝[P.abelianGapDisc m q] a) (𝓝 0) := by
    apply hpoly.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact ((sourceStandardRoot_sq_of_not_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z hz.2).trans
      (sourceAngularSelectedPolynomial_eq_endpoint_factor (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z).symm).symm
  have hH := ((P.analytic_offIndexAbelianFilledQuotient n m hmn (a,q) ⟨haB,hq⟩).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := P.abelianGapDisc m q))
  simpa only [offIndexAbelianNormalizedPrimitive,Function.comp_def,zero_mul] using (tendsto_zero_of_sq_tendsto_zero _ hs).mul hH

theorem offIndexAbelianEndpointIntegral_eq_filled_root_product (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ)
    (hz : z ∈ P.abelianGapDisc m q) :
    P.offIndexAbelianEndpointIntegral n m q z = P.offIndexAbelianNormalizedPrimitive n m (z,q) :=
  P.offIndexAbelianEndpointIntegral_eq_normalized_primitive n m q hq _
    (P.hasDerivAt_offIndexAbelianNormalizedPrimitive n m hmn q hq)
    (P.offIndexAbelianNormalizedPrimitive_endpoint_limit n m hmn q hq _ (by simp)) z hz

theorem analytic_offIndexAbelianEndpointIntegral_joint (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => P.offIndexAbelianEndpointIntegral n m t.2 t.1)
      (P.offIndexAbelianJointDomain m) := by
  intro t ht
  apply (P.analytic_offIndexAbelianNormalizedPrimitive n m hmn t ht).congr
  filter_upwards [(P.offIndexAbelianJointDomain_open m).mem_nhds ht] with s hs
  have hh := (P.offIndexAbelianJointDomain_mem_iff m s).mp hs
  exact (P.offIndexAbelianEndpointIntegral_eq_filled_root_product n m hmn s.2 hh.1 s.1 hh.2).symm

end NLS.KdV.HillProductEquationPatch
