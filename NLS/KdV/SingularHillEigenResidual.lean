import NLS.KdV.SingularHillSpectralEigenvalues
import NLS.FunctionalAnalysis.TwoDimensionalEigenResidual
import NLS.KdV.SingularHillSpectralBasis

/-! The actual source upper-triangular identity on a full original H1
spectral basis, including coincident nonsemisimple complex eigenvalues. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The upper-triangular source identity on ANY actual orthonormal spectral
basis beginning with a lambda-plus eigenfunction. The entire original H1
and H-minus-one equation is retained; no diagonalizability premise is used. -/
theorem exists_singularHill_eigen_residual
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q)
    (lp lm : ℂ) (hmsp : lm ∈ singularHillSpectrum q) (hmi : lm ∈ ball c r)
    (honly : ∀ mu ∈ ball c r, mu ∈ singularHillSpectrum q → mu = lp ∨ mu = lm)
    (b : OrthonormalBasis (Fin 2) ℂ (singularHillL2RieszProjection q c r).range)
    (f phi : FourierLebesgueSpace (2:ℝ) 1 2)
    (hb0 : (b 0).val = singularHillL2DomainInclusion f)
    (hb1 : (b 1).val = singularHillL2DomainInclusion phi)
    (hf : singularHillOperator q f = lp • singularHillDomainInclusion f) :
    ∃ eta : ℂ, singularHillOperator q phi - lp • singularHillDomainInclusion phi =
      -(lp-lm) • singularHillDomainInclusion phi + eta • singularHillDomainInclusion f := by
  let T := singularHillSpectralOperator q c r hr hc
  have hlift0 : singularHillSpectralDomainLift q c r (b 0) = f := by
    apply singularHillL2DomainInclusion_injective
    exact (singularHillSpectralDomainLift_L2 q c r hr hc (b 0)).trans hb0
  have hlift1 : singularHillSpectralDomainLift q c r (b 1) = phi := by
    apply singularHillL2DomainInclusion_injective
    exact (singularHillSpectralDomainLift_L2 q c r hr hc (b 1)).trans hb1
  have hp : T (b 0) = lp • b 0 := by
    apply (singularHillSpectralOperator_eigen_iff q c r hr hc (b 0) lp).mpr
    rwa [hlift0]
  have hm := exists_singularHillSpectralOperator_eigenvector q c r hr hc lm hmsp hmi
  have ho (mu : ℂ) (x : (singularHillL2RieszProjection q c r).range) (hx : x ≠ 0)
      (he : T x = mu • x) : mu = lp ∨ mu = lm := by
    have h := singularHillSpectralOperator_eigenvalue_enclosed q c r hr hc mu x hx he
    exact honly mu h.2 h.1
  obtain ⟨eta,he⟩ := NLS.FunctionalAnalysis.exists_twoDimensional_eigen_residual
    b.toBasis T.toLinearMap lp lm hp hm ho
  have he' : T (b 1) = lm • b 1 + eta • b 0 := by
    simpa only [OrthonormalBasis.coe_toBasis,ContinuousLinearMap.coe_coe] using he
  dsimp only [T] at he'
  have hbase := congrArg (fun x : (singularHillL2RieszProjection q c r).range =>
    singularHillL2BaseInclusion x.val) he'
  rw [singularHillSpectralOperator_base q c r hr hc,hlift1] at hbase
  simp only [Submodule.coe_add,Submodule.coe_smul,map_add,map_smul,hb0,hb1,
    singularHillL2BaseInclusion_domain] at hbase
  exact ⟨eta,by rw [hbase];module⟩

end NLS.KdV
