import NLS.KdV.SingularHillSpectralAction

/-! The actual unbounded periodic expression restricted to its full physical
spectral range, with its faithful original H1 lift and original base action. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The original H1 representative of every physical spectral vector. -/
def singularHillSpectralDomainLift (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    (singularHillL2RieszProjection q c r).range →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (singularHillRieszToH1 q c r).comp
    (singularHillL2BaseInclusion.comp (singularHillL2RieszProjection q c r).range.subtypeL)

/-- The lift represents exactly the SAME physical vector. -/
theorem singularHillSpectralDomainLift_L2
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q)
    (x : (singularHillL2RieszProjection q c r).range) :
    singularHillL2DomainInclusion (singularHillSpectralDomainLift q c r x) = x.val := by
  change singularHillL2RieszProjection q c r x.val = x.val
  obtain ⟨F,hF⟩ := x.property
  rw [← hF]
  exact congrArg (fun T : CircleL2 →L[ℂ] CircleL2 => T F)
    (isIdempotentElem_singularHillL2RieszProjection q c r hr hc)

/-- Every full-base contour lift has its actual physical image in the spectral range. -/
theorem singularHillRieszToH1_L2_mem_range
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q)
    (F : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillL2DomainInclusion (singularHillRieszToH1 q c r F) ∈
      (singularHillL2RieszProjection q c r).range := by
  have hm : singularHillL2BaseInclusion
      (singularHillL2DomainInclusion (singularHillRieszToH1 q c r F)) ∈
        (singularHillRieszProjection q c r).range := by
    rw [singularHillL2BaseInclusion_domain,← singularHillRieszToH1_inclusion q c r hr.le hc]
    exact ⟨F,rfl⟩
  rw [← singularHillL2RieszProjection_range_base q c r hr hc] at hm
  obtain ⟨G,hG,hGe⟩ := hm
  exact singularHillL2BaseInclusion_injective hGe ▸ hG

/-- The actual physical spectral operator, obtained from the SAME native
unbounded expression on the SAME original H1 representatives. -/
def singularHillSpectralOperator
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q) :
    (singularHillL2RieszProjection q c r).range →L[ℂ]
      (singularHillL2RieszProjection q c r).range :=
  ((singularHillL2DomainInclusion.comp (singularHillRieszToH1 q c r)).comp
    ((singularHillOperator q).comp (singularHillSpectralDomainLift q c r))).codRestrict _
      (fun _ => singularHillRieszToH1_L2_mem_range q c r hr hc _)

/-- Its base inclusion is EXACTLY the original unbounded expression,
without a spectral-projection error or added regularity hypothesis. -/
theorem singularHillSpectralOperator_base
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q)
    (x : (singularHillL2RieszProjection q c r).range) :
    singularHillL2BaseInclusion (singularHillSpectralOperator q c r hr hc x).val =
      singularHillOperator q (singularHillSpectralDomainLift q c r x) := by
  let f := singularHillSpectralDomainLift q c r x
  have hf : singularHillL2DomainInclusion f ∈ (singularHillL2RieszProjection q c r).range := by
    rw [show singularHillL2DomainInclusion f = x.val from
      singularHillSpectralDomainLift_L2 q c r hr hc x]
    exact x.property
  have hfix := singularHillDomainRieszProjection_fixed_of_physical_range q c r hr hc f hf
  have hA := singularHillOperator_riesz_intertwine q c r hr.le hc f
  change singularHillOperator q (singularHillDomainRieszProjection q c r f) = _ at hA
  rw [hfix] at hA
  change singularHillL2BaseInclusion (singularHillL2DomainInclusion
    (singularHillRieszToH1 q c r (singularHillOperator q f))) = _
  rw [singularHillL2BaseInclusion_domain,← singularHillRieszToH1_inclusion q c r hr.le hc]
  exact hA.symm

/-- Eigen-equations of the physical restriction are EXACTLY the native
full-domain eigen-equations on its faithful original H1 representatives. -/
theorem singularHillSpectralOperator_eigen_iff
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q)
    (x : (singularHillL2RieszProjection q c r).range) (mu : ℂ) :
    singularHillSpectralOperator q c r hr hc x = mu • x ↔
      singularHillOperator q (singularHillSpectralDomainLift q c r x) =
        mu • singularHillDomainInclusion (singularHillSpectralDomainLift q c r x) := by
  have he : singularHillL2BaseInclusion x.val =
      singularHillDomainInclusion (singularHillSpectralDomainLift q c r x) := by
    rw [← singularHillL2BaseInclusion_domain,singularHillSpectralDomainLift_L2 q c r hr hc]
  constructor
  · intro h
    have h' := congrArg (fun y : (singularHillL2RieszProjection q c r).range =>
      singularHillL2BaseInclusion y.val) h
    simpa only [singularHillSpectralOperator_base q c r hr hc,Submodule.coe_smul,
      map_smul,he] using h'
  · intro h
    apply Subtype.ext
    apply singularHillL2BaseInclusion_injective
    simpa only [singularHillSpectralOperator_base q c r hr hc,Submodule.coe_smul,
      map_smul,he] using h

end NLS.KdV
