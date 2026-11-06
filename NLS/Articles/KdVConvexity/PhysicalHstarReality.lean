import NLS.Articles.KdVConvexity.PhysicalExtensionUniqueness

/-! # Every physical analytic extension is real on the whole positive cone -/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.KdV
namespace NLS.Articles.KdVConvexity.PhysicalHstarExtension

theorem real_and_nonpositive_on_cone (E : PhysicalHstarExtension)
    (a : ActionSpace) (ha : a ∈ positiveQuadrant) :
    (E.hamiltonian a).im=0 ∧ (E.hamiltonian a).re≤0 := by
  obtain ⟨I,U,R,hI,_hU,_hcone,_hR,hrecover,_hbound,_hsign,hV,hpos,hH,hsum,_hzero,hnegative⟩ :=
    exists_global_analytic_actual_contour_extension
  have hnative (q : RealHillWeightedPotential hillH1SpectralWeight) (hm : q.val.val 0=0) (n : ℕ+) :
      R n (baseActionInclusion (physicalHilbertActions hillH1SpectralWeight q)) =
        hillHminusRealGapCubicContourMoment (hillWeightedNativeHminusSource hillH1SpectralWeight q.val)
          (hillWeightedNativeHminusSource_real hillH1SpectralWeight q) n := by
    rw [baseActionInclusion_physicalHilbertActions I hI]
    exact hrecover _ (hillWeightedNativeHminusSource_real hillH1SpectralWeight q)
      (by simpa only [hillWeightedNativeHminusSource_apply] using hm) n
  have hphysical (b : originalPositiveActionDomain) :
      contourHamiltonian R b.val=physicalRenormalizedActionHamiltonian b := by
    have hc := contourHamiltonian_eq_native_physical_H1 R (hH.continuousOn.mono hpos) hnative
      (fun b hb => hsum b (hpos hb)) (originalActionSource b) (originalActionSource_mean_zero b)
    rw [originalActionSource_actions,hillH1LinearActionEnergy_eq_physicalHilbertActions,
      originalActionSource_actions] at hc
    exact hc
  let D : PhysicalHstarExtension := ⟨baseActionInclusion ⁻¹' U,contourHamiltonian R,hV,hpos,hH,
    fun b => hphysical ⟨originalActionInclusion b.val,originalActionInclusion_mem_domain b.val b.property⟩⟩
  have he := (E.eventuallyEq D a ha).eq_of_nhds
  rw [he]
  exact hnegative a ha

end NLS.Articles.KdVConvexity.PhysicalHstarExtension
