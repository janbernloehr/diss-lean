import NLS.KdV.HillHminusIndexedBracketDerivative
import NLS.KdV.HillRealIndexedField

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The genuine Gardner bracket satisfies its exact evolution equation
along every actual original indexed spectral trajectory. The frozen trace
energy is the ACTUAL moving Dirichlet label at the evaluation time. -/
theorem hasDerivAt_hillIndexedCurve_hminus_GardnerBracket
    (k : ℕ+) (γ : ℝ → hillRealSourceSubmodule) (t : ℝ)
    (hγ : HasDerivAt γ (hillRealIndexedDiscriminantField k k.pos (γ t)) t)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource (γ t).val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource (γ t).val)) :
    HasDerivAt (fun s => NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource (γ s).val))
      ((fderiv ℂ (NLS.Poisson.hminusGardnerBracket G
          (fun a => hillHminusDiscriminant a
            (hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 k k.pos)))
          (hillOriginalHminusSource (γ t).val))
          (NLS.Poisson.gardnerHamiltonianVector F (hillOriginalHminusSource (γ t).val)) -
        (fderiv ℂ (NLS.Poisson.hminusGardnerBracket F
          (fun a => hillHminusDiscriminant a
            (hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 k k.pos)))
          (hillOriginalHminusSource (γ t).val))
          (NLS.Poisson.gardnerHamiltonianVector G (hillOriginalHminusSource (γ t).val))) t := by
  let P : hillRealSourceSubmodule →L[ℝ] PeriodOneHminusOne :=
    (hillOriginalHminusSource.restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL
  have hB : AnalyticAt ℂ (NLS.Poisson.hminusGardnerBracket F G)
      (hillOriginalHminusSource (γ t).val) :=
    (NLS.Poisson.gardnerBivector.analyticAt_bilinear _).comp₂
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hF.fderiv)
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hG.fderiv)
  have hd := (hB.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (P.hasFDerivAt.comp_hasDerivAt t hγ)
  change HasDerivAt
    (fun s => NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource (γ s).val))
    ((fderiv ℂ (NLS.Poisson.hminusGardnerBracket F G) (hillOriginalHminusSource (γ t).val))
      (hillOriginalHminusSource (hillIndexedDiscriminantHamiltonianSource
        (⟨(γ t).val,(γ t).property⟩ : RealPeriodOneHillPotential) k k.pos))) t at hd
  rw [hillIndexedSource_hminus_Gardner_derivative
    (⟨(γ t).val,(γ t).property⟩ : RealPeriodOneHillPotential) k F G hF hG] at hd
  exact hd

end NLS.KdV
