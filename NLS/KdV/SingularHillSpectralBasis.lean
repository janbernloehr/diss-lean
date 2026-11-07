import NLS.KdV.SingularHillNormalizedEigenfunction
import NLS.KdV.SingularHillRieszL2
import NLS.FunctionalAnalysis.OrthonormalBasisFirst

/-! Actual orthonormal bases of rank-two periodic spectral spaces, with
an actual normalized eigenfunction as first vector. Both physical vectors
retain representatives in the ENTIRE original periodic H1 domain. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Every rank-two actual spectral space admits the source orthonormal
basis starting with an enclosed actual eigenfunction. Both basis directions
are actual original H1 vectors, including associated-vector directions. -/
theorem exists_singularHill_spectral_orthonormalBasis
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q)
    (hd : Module.finrank ℂ (singularHillL2RieszProjection q c r).range = 2)
    (lambda : ℂ) (hl : lambda ∈ singularHillSpectrum q) (hi : lambda ∈ ball c r) :
    ∃ f : FourierLebesgueSpace (2:ℝ) 1 2,
      singularHillOperator q f = lambda • singularHillDomainInclusion f ∧
      ‖singularHillL2DomainInclusion f‖ = 1 ∧
      ∃ b : OrthonormalBasis (Fin 2) ℂ (singularHillL2RieszProjection q c r).range,
        (b 0).val = singularHillL2DomainInclusion f ∧
        ∀ i : Fin 2, ∃ g : FourierLebesgueSpace (2:ℝ) 1 2,
          singularHillL2DomainInclusion g = (b i).val := by
  obtain ⟨f,hf,hn,_⟩ := exists_singularHill_normalized_eigenfunction q lambda hl
  have hfix : singularHillL2RieszProjection q c r (singularHillL2DomainInclusion f) =
      singularHillL2DomainInclusion f := by
    apply singularHillL2BaseInclusion_injective
    rw [singularHillL2RieszProjection_base q c r hr.le hc,
      singularHillL2BaseInclusion_domain,
      singularHillRieszProjection_eigenvector_inside q c r hr hc lambda hi f hf]
  let x : (singularHillL2RieszProjection q c r).range :=
    ⟨singularHillL2DomainInclusion f,⟨singularHillL2DomainInclusion f,hfix⟩⟩
  let := finiteDimensional_singularHillL2RieszProjection_range q c r hr hc
  obtain ⟨b,hb⟩ := NLS.FunctionalAnalysis.exists_orthonormalBasis_fin_two_first hd x hn
  refine ⟨f,hf,hn,b,congrArg Subtype.val hb,?_⟩
  intro i
  obtain ⟨F,hF⟩ := (b i).property
  exact ⟨singularHillRieszToH1 q c r (singularHillL2BaseInclusion F),hF⟩

end NLS.KdV
