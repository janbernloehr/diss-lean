import NLS.KdV.SingularHillRieszL2

/-! Actual physical L2 contour action on every native enclosed eigenvector. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Every enclosed original native eigenvector is fixed by the SAME physical L2 contour. -/
theorem singularHillL2RieszProjection_eigenvector_inside
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (rho : ℝ) (hrho : 0 < rho)
    (hc : sphere c rho ⊆ singularHillResolventSet q) (z : ℂ) (hz : z ∈ ball c rho)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator q f=z • singularHillDomainInclusion f) :
    singularHillL2RieszProjection q c rho (singularHillL2DomainInclusion f)=singularHillL2DomainInclusion f := by
  apply singularHillL2BaseInclusion_injective
  rw [singularHillL2RieszProjection_base q c rho hrho.le hc,singularHillL2BaseInclusion_domain,
    singularHillRieszProjection_eigenvector_inside q c rho hrho hc z hz f hf]

end NLS.KdV
