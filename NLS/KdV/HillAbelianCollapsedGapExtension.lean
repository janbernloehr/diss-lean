import NLS.KdV.HillAbelianGapEndpointLimits
import NLS.ComplexAnalysis.PrimitiveDiscCutExtension
import NLS.ComplexAnalysis.CauchyFiniteHoles
import NLS.ZakharovShabat.SourceStandardRootLocalContours

/-! Actual off-index Hill differentials have a removable collapsed
cut: the exact zero period forces the regular numerator to vanish.
Their primitives extend across the cut without changing any original
value. One common complex source neighborhood therefore supplies
zero normalization at BOTH endpoints for ALL gaps, collapse included. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem abelianGapNumerator_zero_at_collapsed_gap (P : HillProductEquationPatch) (n m : ℕ+)
    (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hg : AnalyticOnNhd ℂ (fun z => P.abelianGapNumerator n m (z,q))
      (closedBall (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))))
    (hgap : sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) = 0) :
    P.abelianGapNumerator n m (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ),q) = 0 := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hhalf : sourceStandardRootHalfGap (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) = 0 := by
    change (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))/2 = 0
    rw [← sourcePeriodicGapDisplacement_apply,hgap,zero_div]
  have heq : (∮ z in C((D.center:ℂ),D.radius), P.abelianFrequencyDifferential n (z,q)) =
      ∮ z in C((D.center:ℂ),D.radius), P.abelianGapNumerator n m (z,q)/
        sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z := by
    apply circleIntegral.integral_congr D.radius_pos.le
    intro z hz
    exact P.abelianFrequencyDifferential_eq_gap_quotient n m (z,q) (D.sphere_subset_rootDomain hz)
  have hp := P.abelianFrequencyDifferential_period n m q hq D
  rw [if_neg hmn] at hp
  have hzero := (mul_eq_zero.mp hp).resolve_left (inv_ne_zero (by simp [Real.pi_ne_zero]))
  rw [heq,sourceStandardRoot_collapsed_circle_period (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)
    hhalf _ _ _ (D.gap (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))) hg] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (by simp [Real.pi_ne_zero])

theorem abelianGapDisc_primitive_extension_of_collapsed (P : HillProductEquationPatch) (n m : ℕ+)
    (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hg : AnalyticOnNhd ℂ (fun z => P.abelianGapNumerator n m (z,q))
      (closedBall (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))))
    (hgap : sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) = 0)
    (F : ℂ → ℂ) (hF : ∀ z ∈ P.abelianGapDisc m q, HasDerivAt F (P.abelianFrequencyDifferential n (z,q)) z) :
    ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) ∧
      EqOn H F (P.abelianGapDisc m q) ∧
      ∀ a ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)),
        Tendsto F (𝓝[P.abelianGapDisc m q] a) (𝓝 (H a)) := by
  let g : ℂ → ℂ := fun z => P.abelianGapNumerator n m (z,q)
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hτ := D.gap (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))
  have hgzero : g τ = 0 := P.abelianGapNumerator_zero_at_collapsed_gap n m hmn q hq hg hgap
  have hfill : AnalyticOnNhd ℂ (fun z => -dslope g τ z) (ball (D.center:ℂ) D.radius) :=
    (analyticOnNhd_dslope_of_analytic g _ τ (hg.mono ball_subset_closedBall) hτ).neg
  have heq : EqOn (fun z => P.abelianFrequencyDifferential n (z,q)) (fun z => -dslope g τ z)
      (P.abelianGapDisc m q) := by
    intro z hz
    have hroot : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi q) := by
      intro j
      by_cases hj : j = ((m:ℕ):ℤ)
      · subst j; exact hz.2
      · exact D.closedBall_subset_omittedDomain (ball_subset_closedBall hz.1) j hj
    have hne : z ≠ τ := by
      intro he
      exact hz.2 (he ▸ sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))
    change P.abelianFrequencyDifferential n (z,q) = -dslope g τ z
    rw [P.abelianFrequencyDifferential_eq_gap_quotient n m (z,q) hroot,
      sourceStandardRoot_of_zeroGap (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z
        (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap),dslope_of_ne g hne]
    change g z/(τ-z) = -slope g τ z
    rw [slope,smul_eq_mul,vsub_eq_sub,hgzero,sub_zero,div_eq_mul_inv,← neg_sub z τ,inv_neg]
    ring
  obtain ⟨H,hH,hEq,_,hlim⟩ := exists_primitive_disc_cut_extension _ F (fun z => -dslope g τ z) _ _ _ _ D.gap hfill hF heq
  exact ⟨H,hH,hEq,hlim⟩

theorem exists_common_ALL_gap_offIndex_abelian_endpoint_normalization (P : HillProductEquationPatch)
    (q₀ : PeriodOneHminusOne) (hq₀ : q₀ ∈ P.source) (hr : IsRealPeriodOneHminusOne q₀) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ P.source ∧
      ∀ q ∈ V, ∀ n m : ℕ+, m ≠ n → ∃ F : ℂ → ℂ,
        (∀ z ∈ P.abelianGapDisc m q, HasDerivAt F (P.abelianFrequencyDifferential n (z,q)) z) ∧
        Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicLeft (by norm_num) (by norm_num)
          (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 0) ∧
        Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicRight (by norm_num) (by norm_num)
          (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 0) := by
  obtain ⟨V,hV,hqV,hsub,hnum⟩ := P.exists_common_analytic_abelianGapNumerator_neighborhood q₀ hq₀ hr
  refine ⟨V,hV,hqV,hsub,?_⟩
  intro q hq n m hmn
  have hg : AnalyticOnNhd ℂ (fun z => P.abelianGapNumerator n m (z,q))
      (closedBall (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) := by
    intro z hz
    exact (hnum n m (z,q) ⟨hz,hq⟩).comp (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  obtain ⟨F,hF⟩ := P.exists_offIndex_abelianGapDisc_primitive n m hmn q (hsub hq)
  have hlimits : ∃ A : ℂ,
      Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicLeft (by norm_num) (by norm_num)
        (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 A) ∧
      Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicRight (by norm_num) (by norm_num)
        (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 A) := by
    by_cases hgap : sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) = 0
    · obtain ⟨H,_,_,hlim⟩ := P.abelianGapDisc_primitive_extension_of_collapsed n m hmn q (hsub hq) hg hgap F hF
      let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q (hsub hq)).2 ((m:ℕ):ℤ)
        (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
      have he : canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ) =
          canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ) :=
        sub_eq_zero.mp (by simpa only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap] using hgap)
      refine ⟨_,hlim _ (D.gap (left_mem_segment ℝ _ _)),?_⟩
      rw [he]
      exact hlim _ (D.gap (left_mem_segment ℝ _ _))
    · exact P.abelianGapDisc_primitive_common_endpoint_limit n m q (hsub hq) hg hgap F hF
  obtain ⟨A,hA,hB⟩ := hlimits
  exact ⟨fun z => F z-A,fun z hz => (hF z hz).sub_const A,by simpa only [sub_self] using hA.sub_const A,
    by simpa only [sub_self] using hB.sub_const A⟩

end NLS.KdV.HillProductEquationPatch
