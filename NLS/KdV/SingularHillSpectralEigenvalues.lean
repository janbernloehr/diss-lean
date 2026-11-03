import NLS.KdV.SingularHillSpectralOperator
import NLS.KdV.SingularHillNormalizedEigenfunction

/-! The actual physical spectral restriction has exactly the enclosed
original eigenvalues. No artificial eigenvalues arise from projection of
the unbounded expression, and associated-vector directions are retained. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- An actual nonzero physical spectral vector has a nonzero original H1 lift. -/
theorem singularHillSpectralDomainLift_ne_zero
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q)
    (x : (singularHillL2RieszProjection q c r).range) (hx : x ≠ 0) :
    singularHillSpectralDomainLift q c r x ≠ 0 := by
  intro he
  apply hx
  apply Subtype.ext
  have h := singularHillSpectralDomainLift_L2 q c r hr hc x
  rw [he,map_zero] at h
  exact h.symm

/-- Every eigenvalue of the actual physical restriction is a genuine
full-domain original eigenvalue enclosed by the actual source circle. -/
theorem singularHillSpectralOperator_eigenvalue_enclosed
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q)
    (mu : ℂ) (x : (singularHillL2RieszProjection q c r).range) (hx : x ≠ 0)
    (h : singularHillSpectralOperator q c r hr hc x = mu • x) :
    mu ∈ singularHillSpectrum q ∧ mu ∈ ball c r := by
  let f := singularHillSpectralDomainLift q c r x
  have hf0 : f ≠ 0 := singularHillSpectralDomainLift_ne_zero q c r hr hc x hx
  have he : singularHillOperator q f = mu • singularHillDomainInclusion f :=
    (singularHillSpectralOperator_eigen_iff q c r hr hc x mu).mp h
  have hsp : mu ∈ singularHillSpectrum q := (mem_singularHillSpectrum_iff q mu).mpr ⟨f,hf0,he⟩
  refine ⟨hsp,?_⟩
  by_contra hi
  by_cases hb : mu ∈ closedBall c r
  · have hs : mu ∈ sphere c r := mem_sphere.mpr
      (le_antisymm (mem_closedBall.mp hb) (not_lt.mp hi))
    exact hsp (hc hs)
  · have hfmem : singularHillL2DomainInclusion f ∈ (singularHillL2RieszProjection q c r).range := by
      rw [show singularHillL2DomainInclusion f = x.val from
        singularHillSpectralDomainLift_L2 q c r hr hc x]
      exact x.property
    have hfix := singularHillDomainRieszProjection_fixed_of_physical_range q c r hr hc f hfmem
    have hfixed : singularHillRieszProjection q c r (singularHillDomainInclusion f) =
        singularHillDomainInclusion f := by
      rw [singularHillRieszToH1_inclusion q c r hr.le hc]
      exact congrArg singularHillDomainInclusion hfix
    have hzero := singularHillRieszProjection_eigenvector_outside q c r hr hc mu hb f he
    exact hf0 (singularHillDomainInclusion_injective
      (by simpa only [map_zero] using hfixed.symm.trans hzero))

/-- Every enclosed actual original eigenvalue occurs in the physical restriction. -/
theorem exists_singularHillSpectralOperator_eigenvector
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q) (mu : ℂ)
    (hsp : mu ∈ singularHillSpectrum q) (hi : mu ∈ ball c r) :
    ∃ x : (singularHillL2RieszProjection q c r).range,
      x ≠ 0 ∧ singularHillSpectralOperator q c r hr hc x = mu • x := by
  obtain ⟨f,hf,hn,_⟩ := exists_singularHill_normalized_eigenfunction q mu hsp
  have hfix : singularHillL2RieszProjection q c r (singularHillL2DomainInclusion f) =
      singularHillL2DomainInclusion f := by
    apply singularHillL2BaseInclusion_injective
    rw [singularHillL2RieszProjection_base q c r hr.le hc,
      singularHillL2BaseInclusion_domain,
      singularHillRieszProjection_eigenvector_inside q c r hr hc mu hi f hf]
  let x : (singularHillL2RieszProjection q c r).range :=
    ⟨singularHillL2DomainInclusion f,⟨singularHillL2DomainInclusion f,hfix⟩⟩
  have hlift : singularHillSpectralDomainLift q c r x = f := by
    apply singularHillL2DomainInclusion_injective
    exact singularHillSpectralDomainLift_L2 q c r hr hc x
  refine ⟨x,?_,?_⟩
  · intro hx
    have hx0 : singularHillL2DomainInclusion f = 0 := congrArg Subtype.val hx
    rw [hx0,norm_zero] at hn
    norm_num at hn
  · apply (singularHillSpectralOperator_eigen_iff q c r hr hc x mu).mpr
    rwa [hlift]

end NLS.KdV
