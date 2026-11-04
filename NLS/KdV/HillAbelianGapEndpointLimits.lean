import NLS.KdV.HillOffIndexAbelianPrimitives
import NLS.ComplexAnalysis.QuadraticRootPrimitiveEndpointLimits
import NLS.ComplexAnalysis.CosinePrimitiveEndpointAgreement

/-! Full relative endpoint limits of ACTUAL Hill Abelian primitives
on the original complex gap discs. For noncollapsed gaps the limits
at BOTH ends agree. Off-index zero periods supply a primitive, so it
can be normalized to zero at both endpoints, BEFORE ALL path choices. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem abelianGapDisc_primitive_common_endpoint_limit (P : HillProductEquationPatch)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hg : AnalyticOnNhd ℂ (fun z => P.abelianGapNumerator n m (z,q))
      (closedBall (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))))
    (hgap : sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) ≠ 0)
    (F : ℂ → ℂ) (hF : ∀ z ∈ P.abelianGapDisc m q, HasDerivAt F (P.abelianFrequencyDifferential n (z,q)) z) :
    ∃ A : ℂ,
      Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicLeft (by norm_num) (by norm_num)
        (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 A) ∧
      Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicRight (by norm_num) (by norm_num)
        (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 A) := by
  let l := canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ)
  let r := canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ)
  let Ω := ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))
  let g : ℂ → ℂ := fun z => P.abelianGapNumerator n m (z,q)
  let Q := sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hlr : l ≠ r := by
    intro h
    apply hgap
    rw [sourcePeriodicGapDisplacement_apply]
    exact sub_eq_zero.mpr h.symm
  have hQ : ContinuousOn Q (Ω \ segment ℝ l r) := by
    intro z hz
    exact (sourceStandardRoot_analyticAt (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z hz.2).continuousAt.continuousWithinAt
  have hsq : ∀ z ∈ Ω \ segment ℝ l r, Q z^2 = (l-z)*(r-z) := by
    intro z hz
    exact sourceStandardRoot_sq_of_not_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z hz.2
  have hderiv : ∀ z ∈ Ω \ segment ℝ l r, HasDerivAt F (g z/Q z) z := by
    intro z hz
    have hroot : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi q) := by
      intro j
      by_cases hj : j = ((m:ℕ):ℤ)
      · subst j; exact hz.2
      · exact D.closedBall_subset_omittedDomain (ball_subset_closedBall hz.1) j hj
    rw [← P.abelianFrequencyDifferential_eq_gap_quotient n m (z,q) hroot]
    exact hF z hz
  obtain ⟨A,B,hA,hB⟩ := exists_quadratic_root_primitive_endpoint_limits g Q F _ l r _ hlr D.gap hg.continuousOn hQ hsq hderiv
  have he : A = B := by
    let τ := (l+r)/2
    let δ := (r-l)/2
    have hl : τ-δ = l := by dsimp [τ,δ]; ring
    have hr : τ+δ = r := by dsimp [τ,δ]; ring
    apply primitive_cosine_gap_boundary_values_eq g Q F Ω τ δ A B isOpen_ball
      (div_ne_zero (sub_ne_zero.mpr hlr.symm) (by norm_num))
    · rw [hl,hr]; exact D.gap
    · exact hg.mono ball_subset_closedBall
    · rw [hl,hr]; exact hQ
    · rw [hl,hr]; exact hsq
    · rw [hl,hr]; exact hderiv
    · rw [hl,hr]; exact hA
    · rw [hl,hr]; exact hB
  exact ⟨A,hA,he.symm ▸ hB⟩

theorem exists_common_offIndex_abelian_endpoint_normalization (P : HillProductEquationPatch)
    (q₀ : PeriodOneHminusOne) (hq₀ : q₀ ∈ P.source) (hr : IsRealPeriodOneHminusOne q₀) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ P.source ∧
      ∀ q ∈ V, ∀ n m : ℕ+, m ≠ n →
        sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) ≠ 0 →
        ∃ F : ℂ → ℂ,
          (∀ z ∈ P.abelianGapDisc m q, HasDerivAt F (P.abelianFrequencyDifferential n (z,q)) z) ∧
          Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicLeft (by norm_num) (by norm_num)
            (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 0) ∧
          Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicRight (by norm_num) (by norm_num)
            (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 0) := by
  obtain ⟨V,hV,hqV,hsub,hnum⟩ := P.exists_common_analytic_abelianGapNumerator_neighborhood q₀ hq₀ hr
  refine ⟨V,hV,hqV,hsub,?_⟩
  intro q hq n m hmn hgap
  obtain ⟨F,hF⟩ := P.exists_offIndex_abelianGapDisc_primitive n m hmn q (hsub hq)
  have hg : AnalyticOnNhd ℂ (fun z => P.abelianGapNumerator n m (z,q))
      (closedBall (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) := by
    intro z hz
    exact (hnum n m (z,q) ⟨hz,hq⟩).comp (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  obtain ⟨A,hA,hB⟩ := P.abelianGapDisc_primitive_common_endpoint_limit n m q (hsub hq) hg hgap F hF
  refine ⟨fun z => F z-A,fun z hz => (hF z hz).sub_const A,?_,?_⟩
  · simpa only [sub_self] using hA.sub_const A
  · simpa only [sub_self] using hB.sub_const A

end NLS.KdV.HillProductEquationPatch
