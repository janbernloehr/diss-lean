import NLS.Articles.KdVConvexity.PhysicalExtensionUniqueness

/-! # Continuing physical frequencies on one common Hilbert neighborhood

This isolates precisely the remaining input concerning the original
ell^(-1,1) frequency extension: once constructed there with physical
recovery, coordinatewise analyticity suffices to identify ALL frequencies
on ONE neighborhood of the ENTIRE positive ell2 cone. No uniform complex
germ radius over the coordinate index is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVConvexity

theorem exists_common_physical_frequency_domain
    (E : PhysicalHstarExtension)
    (U0 : Set BaseActionSpace) (hU0 : IsOpen U0)
    (hcone : WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U0)
    (ω : ℕ+ → BaseActionSpace → ℂ) (hω : ∀ n, AnalyticOnNhd ℂ (ω n) U0)
    (hphysical : ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
      ω n (baseActionInclusion (originalActionInclusion b.val))=originalPhysicalFrequency b n) :
    ∃ V : Set ActionSpace, IsOpen V ∧ positiveQuadrant ⊆ V ∧
      V ⊆ E.domain ∩ baseActionInclusion ⁻¹' U0 ∧
      ∀ a ∈ V, ∀ n : ℕ+,
        actionGradient E.hamiltonian a n=ω n (baseActionInclusion a)-
          ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ) := by
  let W := E.domain ∩ baseActionInclusion ⁻¹' U0
  have hW : IsOpen W := E.isOpen.inter (hU0.preimage baseActionInclusion.continuous)
  have hcW : positiveQuadrant ⊆ W := fun a ha =>
    ⟨E.contains_cone ha,hcone (baseActionInclusion_mem_nonnegative a ha)⟩
  let f : ℕ+ → ActionSpace → ℂ := fun n a => actionGradient E.hamiltonian a n
  let g : ℕ+ → ActionSpace → ℂ := fun n a => ω n (baseActionInclusion a)-
    ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)
  have hf (n : ℕ+) : AnalyticOnNhd ℂ (f n) W := fun a ha =>
    (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).analyticAt _ |>.comp
      (analyticOnNhd_actionGradient _ E.analytic a ha.1)
  have hg (n : ℕ+) : AnalyticOnNhd ℂ (g n) W := fun a ha =>
    ((hω n _ ha.2).comp (baseActionInclusion.analyticAt a)).sub analyticAt_const
  have he (n : ℕ+) (a : ActionSpace) (_ha : a ∈ W) (hapos : a ∈ originalPositiveActionDomain) :
      f n a=g n a := by
    obtain ⟨b,hb,hba⟩ := original_domain_has_weighted_representative a hapos
    rw [←hba]
    change actionGradient E.hamiltonian (originalActionInclusion b) n =
      ω n (baseActionInclusion (originalActionInclusion b)) - _
    rw [hphysical ⟨b,hb⟩ n,originalPhysicalFrequency_eq_gradient E ⟨b,hb⟩ n]
    exact (add_sub_cancel_left _ _).symm
  let V := ⋃₀ {T : Set ActionSpace | ∃ c ∈ positiveQuadrant, ∃ r : ℝ,
    0 < r ∧ T=ball c r ∧ T ⊆ W}
  have hV : IsOpen V := isOpen_sUnion (by
    rintro T ⟨c,_hc,r,_hr,rfl,_hT⟩
    exact isOpen_ball)
  have hpos : positiveQuadrant ⊆ V := by
    intro c hc
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds (hcW hc))
    exact mem_sUnion.mpr ⟨ball c r,⟨c,hc,r,hr,rfl,hball⟩,mem_ball_self hr⟩
  refine ⟨V,hV,hpos,?_,?_⟩
  · intro a ha
    obtain ⟨T,⟨_c,_hc,_r,_hr,_heq,hTW⟩,haT⟩ := mem_sUnion.mp ha
    exact hTW haT
  · intro a ha n
    obtain ⟨T,⟨c,hc,r,hr,rfl,hTW⟩,haT⟩ := mem_sUnion.mp ha
    have hlocal := eventuallyEq_of_original_domain_agreement (f n) (g n) W hW
      (hf n) (hg n) (he n) c (hcW hc) hc
    have hall := NLS.ComplexAnalysis.DifferentiableOn.eqOn_of_convex_of_eventuallyEq
      (f n) (g n) (ball c r) isOpen_ball (convex_ball c r)
      ((hf n).mono hTW).differentiableOn ((hg n).mono hTW).differentiableOn
      c (mem_ball_self hr) hlocal
    exact hall haT

end NLS.Articles.KdVConvexity
