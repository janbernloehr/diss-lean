import NLS.Articles.KdVPseudomeasures.OriginalHillSmoothPhysicalSolutions

/-! The actual rough solution characterized by EVERY approximating
family of literal smooth physical PDE solutions in the genuine H4/H1
strong model. Smooth approximating solutions are CONSTRUCTED, so the
universal characterization is nonvacuous and determines a unique curve.
The adapter from arbitrary jointly smooth space-time functions to this
strong solution model remains a separate source-fidelity obligation. -/
noncomputable section
open Set Filter Topology NLS.KdV NLS.WeightedCoeff
open scoped ContDiff
namespace NLS.Articles.KdVPseudomeasures

def HillRoughSolutionBySmoothApproximation (q : HillRealMeanZeroSource)
    (γ : ℝ → HillRealMeanZeroSource) : Prop :=
  Continuous γ ∧ γ 0=q ∧
  ∀ Γ : ℕ → ℝ → RealSignedHilbert (signedStepOrder 0 4),
    (∀ j, HillSmoothStrongKdVSolution (Γ j)) →
    Tendsto (fun j => hillIntegerSourceInclusion 4 (Γ j 0)) atTop (𝓝 q) →
    ∀ t, Tendsto (fun j => hillIntegerSourceInclusion 4 (Γ j t)) atTop (𝓝 (γ t))

theorem exists_hillSmoothStrong_approximating_solutions (q : HillRealMeanZeroSource) :
    ∃ Γ : ℕ → ℝ → RealSignedHilbert (signedStepOrder 0 4),
      (∀ j, HillSmoothStrongKdVSolution (Γ j)) ∧
      Tendsto (fun j => hillIntegerSourceInclusion 4 (Γ j 0)) atTop (𝓝 q) := by
  have hex (j : ℕ) : ∃ a : RealSignedHilbert (signedStepOrder 0 4),
      hillIntegerSourceInclusion 4 a=hillRoughFiniteGapApproximation q j := by
    apply hillReal_has_integer_representative_of_mem_sobolev
    exact hillRealFiniteGap_mem_all_sobolev _ (hillRoughFiniteGapApproximation_mem q j) _
      (by rw [hillIntegerSobolev_source_order]; positivity)
  let a := fun j : ℕ => Classical.choose (hex j)
  have ha (j : ℕ) : hillIntegerSourceInclusion 4 (a j)=hillRoughFiniteGapApproximation q j :=
    Classical.choose_spec (hex j)
  have hs (j : ℕ) : ContDiff ℝ ∞ (hillPhysicalH4Synthesis (a j)) := by
    apply contDiff_hillH1_physical_synthesis_of_smooth_locus
    rw [hillIntegerSourceOrderInclusion_rough,ha]
    exact hillRealFiniteGap_subset_smooth (hillRoughFiniteGapApproximation_mem q j)
  refine ⟨fun j t => hillIntegerCanonicalKdVFlow 4 (a j) t,
    fun j => hillCanonicalFlow_is_smoothStrongKdVSolution (a j) (hs j),?_⟩
  simpa only [hillIntegerCanonicalKdVFlow_zero,ha] using hillRoughFiniteGapApproximation_tendsto q

theorem hillCanonicalFlow_is_roughSolutionBySmoothApproximation (q : HillRealMeanZeroSource) :
    HillRoughSolutionBySmoothApproximation q (hillRoughCanonicalKdVFlow q) := by
  have ht : Continuous (hillRoughCanonicalKdVFlow q) := by
    have hi : Continuous (fun t : ℝ => (t,q)) := continuous_id.prodMk continuous_const
    simpa only [Function.comp_def] using! continuous_hillRoughCanonicalKdVFlow.comp hi
  refine ⟨ht,hillRoughCanonicalKdVFlow_zero q,?_⟩
  intro Γ hΓ hinit t
  have hc : Continuous (fun p : HillRealMeanZeroSource => hillRoughCanonicalKdVFlow p t) := by
    have hi : Continuous (fun p : HillRealMeanZeroSource => (t,p)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using! continuous_hillRoughCanonicalKdVFlow.comp hi
  have he : (fun j => hillIntegerSourceInclusion 4 (Γ j t))=
      (fun j => hillRoughCanonicalKdVFlow (hillIntegerSourceInclusion 4 (Γ j 0)) t) := by
    funext j
    rw [hillSmoothStrongKdVSolution_eq_canonicalFlow (Γ j) (hΓ j) t,hillIntegerCanonicalKdVFlow_inclusion]
  rw [he]
  exact hc.continuousAt.tendsto.comp hinit

theorem hillRoughSolutionBySmoothApproximation_unique
    (q : HillRealMeanZeroSource) (γ : ℝ → HillRealMeanZeroSource)
    (hγ : HillRoughSolutionBySmoothApproximation q γ) : γ=hillRoughCanonicalKdVFlow q := by
  obtain ⟨Γ,hΓ,hinit⟩ := exists_hillSmoothStrong_approximating_solutions q
  have hc := hillCanonicalFlow_is_roughSolutionBySmoothApproximation q
  funext t
  exact tendsto_nhds_unique (hγ.2.2 Γ hΓ hinit t) (hc.2.2 Γ hΓ hinit t)

theorem existsUnique_hillRoughSolutionBySmoothApproximation (q : HillRealMeanZeroSource) :
    ∃! γ : ℝ → HillRealMeanZeroSource, HillRoughSolutionBySmoothApproximation q γ := by
  exact ⟨hillRoughCanonicalKdVFlow q,hillCanonicalFlow_is_roughSolutionBySmoothApproximation q,
    fun γ hγ => hillRoughSolutionBySmoothApproximation_unique q γ hγ⟩

end NLS.Articles.KdVPseudomeasures
