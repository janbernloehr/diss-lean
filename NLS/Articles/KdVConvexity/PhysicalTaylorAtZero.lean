import NLS.Articles.KdVConvexity.ActionTaylorAtZero
import NLS.Articles.KdVConvexity.PhysicalExtensionUniqueness

/-! # The physical KdV gradient and its full minus-six derivative at zero -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.Articles.KdVConvexity
open NLS.KdV

theorem zero_mem_positiveQuadrant : (0 : ActionSpace) ∈ positiveQuadrant := by
  intro n
  simp

/-- The actual globally analytic contour extension has the physical
normalization at zero, including its full bounded gradient derivative. -/
theorem exists_physicalHstarExtension_with_Taylor_at_zero :
    ∃ E : PhysicalHstarExtension, E.hamiltonian 0=0 ∧ actionGradient E.hamiltonian 0=0 ∧
      fderiv ℂ (actionGradient E.hamiltonian) 0=
        (-6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace := by
  obtain ⟨I,U,R,hI,_hU,_hcone,_hR,hrecover,_hbound,hsign,hV,hpos,hH,hsum,hzero,_hnegative⟩ :=
    exists_global_analytic_actual_contour_extension
  have hnative (q : RealHillWeightedPotential hillH1SpectralWeight) (hm : q.val.val 0=0) (n : ℕ+) :
      R n (baseActionInclusion (physicalHilbertActions hillH1SpectralWeight q)) =
        hillHminusRealGapCubicContourMoment (hillWeightedNativeHminusSource hillH1SpectralWeight q.val)
          (hillWeightedNativeHminusSource_real hillH1SpectralWeight q) n := by
    rw [baseActionInclusion_physicalHilbertActions I hI]
    exact hrecover _ (hillWeightedNativeHminusSource_real hillH1SpectralWeight q)
      (by simpa only [hillWeightedNativeHminusSource_apply] using hm) n
  have hphysical (a : originalPositiveActionDomain) :
      contourHamiltonian R a.val=physicalRenormalizedActionHamiltonian a := by
    have hc := contourHamiltonian_eq_native_physical_H1 R (hH.continuousOn.mono hpos) hnative
      (fun a ha => hsum a (hpos ha)) (originalActionSource a) (originalActionSource_mean_zero a)
    rw [originalActionSource_actions,hillH1LinearActionEnergy_eq_physicalHilbertActions,
      originalActionSource_actions] at hc
    exact hc
  let E : PhysicalHstarExtension := ⟨baseActionInclusion ⁻¹' U,contourHamiltonian R,hV,hpos,hH,
    fun b => hphysical ⟨originalActionInclusion b.val,originalActionInclusion_mem_domain b.val b.property⟩⟩
  have hRzero (a : ActionSpace) (ha : a ∈ positiveQuadrant) (n : ℕ+) (hn : a n=0) :
      R n (baseActionInclusion a)=0 := by
    apply ((hsign _ (baseActionInclusion_mem_nonnegative a ha) n).2.2).mpr
    simpa only [baseActionInclusion_apply,Equiv.apply_symm_apply] using hn
  have ht := actionTaylor_of_finite_ray_limits (contourHamiltonian R)
    (hH 0 (hpos zero_mem_positiveQuadrant)) hzero
    (tendsto_contourHamiltonian_div_finite_action_ray_sq I hI R hrecover hRzero)
  exact ⟨E,hzero,ht⟩

namespace PhysicalHstarExtension

/-- Every physical global extension has the same zero value and Taylor
operator: these are intrinsic to the physical Hamiltonian. -/
theorem Taylor_at_zero (E : PhysicalHstarExtension) :
    E.hamiltonian 0=0 ∧ actionGradient E.hamiltonian 0=0 ∧
      fderiv ℂ (actionGradient E.hamiltonian) 0=
        (-6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace := by
  obtain ⟨D,hD0,hDgrad,hDderiv⟩ := exists_physicalHstarExtension_with_Taylor_at_zero
  have he := E.eventuallyEq D 0 zero_mem_positiveQuadrant
  have hgrad : actionGradient E.hamiltonian =ᶠ[𝓝 0] actionGradient D.hamiltonian := by
    filter_upwards [he.fderiv (𝕜 := ℂ)] with a ha
    exact congrArg actionCotangentCoefficients ha
  exact ⟨(he.eq_of_nhds).trans hD0,(hgrad.eq_of_nhds).trans hDgrad,
    hgrad.fderiv_eq.trans hDderiv⟩

end PhysicalHstarExtension
end NLS.Articles.KdVConvexity
