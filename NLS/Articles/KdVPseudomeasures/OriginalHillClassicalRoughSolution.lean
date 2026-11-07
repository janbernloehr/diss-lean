import NLS.Articles.KdVPseudomeasures.OriginalHillClassicalApproximationDefinition

/-! Nonvacuity and uniqueness of the rough solution characterized by
EVERY sequence of jointly smooth classical KdV solutions. Actual finite
native truncations supply a jointly smooth approximating family for
EVERY rough initial potential. -/
noncomputable section
open Set Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem exists_hillClassical_approximating_solutions (q : HillRealMeanZeroSource) :
    ∃ (F : ℕ → ℝ × ℝ → ℂ) (hF : ∀ j, HillClassicalSpaceTimeKdVSolution (F j)),
      Tendsto (fun j => hillClassicalSolutionRoughCurve (F j) (hF j) 0) atTop (𝓝 q) := by
  have hex (j : ℕ) : ∃ a : RealSignedHilbert (signedStepOrder 0 4),
      hillIntegerSourceInclusion 4 a = hillRoughFiniteGapApproximation q j := by
    apply hillReal_has_integer_representative_of_mem_sobolev
    exact hillRealFiniteGap_mem_all_sobolev _ (hillRoughFiniteGapApproximation_mem q j) _
      (by rw [hillIntegerSobolev_source_order]; positivity)
  let a := fun j : ℕ => Classical.choose (hex j)
  have ha (j : ℕ) : hillIntegerSourceInclusion 4 (a j) = hillRoughFiniteGapApproximation q j :=
    Classical.choose_spec (hex j)
  have hfin (j : ℕ) (k : ℤ) (hk : k ∉ NLS.Coeff.lowFrequencies j) :
      ((hillIntegerSobolevEquiv 4).equiv (a j)).val.val.val k = 0 := by
    rw [← hillIntegerTargetInclusion_apply 4, hillIntegerSobolevEquiv_inclusion, ha,
      hillRoughFiniteGapApproximation_native, fourierRealZeroTruncate_apply]
    exact if_neg (by simpa only [NLS.Coeff.mem_lowFrequencies] using hk)
  let F := fun j : ℕ => fun u : ℝ × ℝ => hillPhysicalH4Synthesis (hillIntegerCanonicalKdVFlow 4 (a j) u.1) u.2
  have hF (j : ℕ) : HillClassicalSpaceTimeKdVSolution (F j) :=
    hillFiniteNative_is_classicalSpaceTimeSolution (a j) (NLS.Coeff.lowFrequencies j) (hfin j)
  have he (j : ℕ) : hillClassicalSolutionRoughCurve (F j) (hF j) 0 = hillRoughFiniteGapApproximation q j := by
    rw [hillClassicalSolutionRoughCurve_of_physicalStrongCurve, hillIntegerCanonicalKdVFlow_zero, ha]
  refine ⟨F,hF,?_⟩
  simpa only [he] using hillRoughFiniteGapApproximation_tendsto q

theorem hillCanonicalFlow_is_roughSolutionByClassicalApproximation (q : HillRealMeanZeroSource) :
    HillRoughSolutionByClassicalApproximation q (hillRoughCanonicalKdVFlow q) := by
  have hs := hillCanonicalFlow_is_roughSolutionBySmoothApproximation q
  refine ⟨hs.1,hs.2.1,?_⟩
  intro F hF hi t
  have hc : Continuous (fun p : HillRealMeanZeroSource => hillRoughCanonicalKdVFlow p t) := by
    have hj : Continuous (fun p : HillRealMeanZeroSource => (t,p)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using! continuous_hillRoughCanonicalKdVFlow.comp hj
  have he : (fun j => hillClassicalSolutionRoughCurve (F j) (hF j) t) =
      (fun j => hillRoughCanonicalKdVFlow (hillClassicalSolutionRoughCurve (F j) (hF j) 0) t) :=
    funext (fun j => hillClassicalSolutionRoughCurve_eq_canonicalFlow (F j) (hF j) t)
  rw [he]
  exact hc.continuousAt.tendsto.comp hi

theorem hillRoughSolutionByClassicalApproximation_unique
    (q : HillRealMeanZeroSource) (γ : ℝ → HillRealMeanZeroSource)
    (hγ : HillRoughSolutionByClassicalApproximation q γ) : γ = hillRoughCanonicalKdVFlow q := by
  obtain ⟨F,hF,hi⟩ := exists_hillClassical_approximating_solutions q
  have hc := hillCanonicalFlow_is_roughSolutionByClassicalApproximation q
  funext t
  exact tendsto_nhds_unique (hγ.2.2 F hF hi t) (hc.2.2 F hF hi t)

theorem existsUnique_hillRoughSolutionByClassicalApproximation (q : HillRealMeanZeroSource) :
    ∃! γ : ℝ → HillRealMeanZeroSource, HillRoughSolutionByClassicalApproximation q γ :=
  ⟨hillRoughCanonicalKdVFlow q,hillCanonicalFlow_is_roughSolutionByClassicalApproximation q,
    fun γ hγ => hillRoughSolutionByClassicalApproximation_unique q γ hγ⟩

theorem hillRoughSolutionByClassicalApproximation_iff_strongApproximation
    (q : HillRealMeanZeroSource) (γ : ℝ → HillRealMeanZeroSource) :
    HillRoughSolutionByClassicalApproximation q γ ↔ HillRoughSolutionBySmoothApproximation q γ := by
  constructor
  · intro hγ
    rw [hillRoughSolutionByClassicalApproximation_unique q γ hγ]
    exact hillCanonicalFlow_is_roughSolutionBySmoothApproximation q
  · intro hγ
    rw [hillRoughSolutionBySmoothApproximation_unique q γ hγ]
    exact hillCanonicalFlow_is_roughSolutionByClassicalApproximation q

end NLS.Articles.KdVPseudomeasures
