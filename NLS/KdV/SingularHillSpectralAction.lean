import NLS.KdV.SingularHillRieszL2

/-! The actual unbounded periodic expression acts inside its physical
spectral range. Its L2 output is proved from the actual contour domain
preservation and intertwining, rather than assumed as extra regularity. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- A native H1 vector in the physical spectral range is fixed by the
ACTUAL H1-domain projection. -/
theorem singularHillDomainRieszProjection_fixed_of_physical_range
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillL2DomainInclusion f ∈ (singularHillL2RieszProjection q c r).range) :
    singularHillDomainRieszProjection q c r f = f := by
  obtain ⟨F,hF⟩ := hf
  have hfix : singularHillL2RieszProjection q c r (singularHillL2DomainInclusion f) =
      singularHillL2DomainInclusion f := by
    rw [← hF]
    exact congrArg (fun T : CircleL2 →L[ℂ] CircleL2 => T F)
      (isIdempotentElem_singularHillL2RieszProjection q c r hr hc)
  apply singularHillL2DomainInclusion_injective
  rw [← singularHillL2RieszProjection_domain q c r f]
  exact hfix

/-- On EVERY original H1 representative of a physical spectral vector,
the ACTUAL unbounded expression has a physical L2 output in that SAME
spectral range. Neither an L2-action premise nor semisimplicity is assumed. -/
theorem exists_singularHillOperator_spectral_L2_action
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillL2DomainInclusion f ∈ (singularHillL2RieszProjection q c r).range) :
    ∃ G : CircleL2, singularHillL2BaseInclusion G = singularHillOperator q f ∧
      G ∈ (singularHillL2RieszProjection q c r).range := by
  have hfix := singularHillDomainRieszProjection_fixed_of_physical_range q c r hr hc f hf
  have hA := singularHillOperator_riesz_intertwine q c r hr.le hc f
  change singularHillOperator q (singularHillDomainRieszProjection q c r f) = _ at hA
  rw [hfix] at hA
  have hmem : singularHillOperator q f ∈ (singularHillRieszProjection q c r).range :=
    ⟨singularHillOperator q f,hA.symm⟩
  rw [← singularHillL2RieszProjection_range_base q c r hr hc] at hmem
  obtain ⟨G,hG,hGe⟩ := hmem
  exact ⟨G,hGe,hG⟩

end NLS.KdV
