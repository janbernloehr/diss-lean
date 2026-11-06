import NLS.MKdV.QuasiHillJointAnalytic
import NLS.ZakharovShabat.ContinuousPotentialSource
import NLS.MKdV.PeriodOneMiuraCurveCLM
import NLS.ZakharovShabat.ClassicalDomainPotential
import NLS.ZakharovShabat.SourceSobolevEmbedding

/-! Literal physical diagonal-source and Sobolev comparisons, separated from primitive sheet continuation. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat
namespace NLS.MKdV

def miuraDiagonalCurveCLM : Curve ℂ →L[ℂ] Curve (ℂ × ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1)
    ((ContinuousLinearMap.id ℂ ℂ).prod (ContinuousLinearMap.id ℂ ℂ))

def miuraDiagonalSourceCLM : Curve ℂ →L[ℂ] CoeffPair 2 :=
  continuousPotentialSource.comp miuraDiagonalCurveCLM


theorem canonicalDiscriminant_miuraDiagonalSource (U : Curve ℂ) (z : ℂ) :
    canonicalDiscriminant (by simp) (periodOnePotential (miuraDiagonalSourceCLM U)) z =
      quasiHillDiscriminant U (z^2) := by
  rw [miuraDiagonalSourceCLM,ContinuousLinearMap.comp_apply,
    canonicalDiscriminant_continuousPotentialSource]
  exact (quasiHillDiscriminant_eq_ZS U _ (fun _ => rfl) z).symm


theorem miuraDiagonalSource_periodOneMiuraCurve (a : ScalarDomain 2) :
    miuraDiagonalSourceCLM (periodOneMiuraCurve a) = sobolevSourceInclusion (a,a) := by
  let c : Domain 2 := (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a)
  have hper : periodOnePotential (sobolevSourceInclusion (a,a)) = domainInclusion c := by
    apply Prod.ext <;> ext n <;>
      simp [periodOnePotential_apply,domainInclusion_apply,c,scalarInclusion_apply,
        Coeff.periodDoubleSobolev_apply,sobolevSourceInclusion]
  have hcurve : physicalDomainCurve c = miuraDiagonalCurveCLM (periodOneMiuraCurve a) := rfl
  have hp : physicalBase (periodOnePotential (sobolevSourceInclusion (a,a)))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        extend (miuraDiagonalCurveCLM (periodOneMiuraCurve a)) := by
    rw [hper,← hcurve]
    exact physicalBase_eq_extend_physicalDomainCurve c
  apply sourcePhysicalL2Equiv.injective
  change sourcePhysicalL2Equiv (sourcePhysicalL2Equiv.symm
    (continuousPotentialL2CLM (miuraDiagonalCurveCLM (periodOneMiuraCurve a)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,sourcePhysicalL2Equiv_apply,
    continuousPotentialL2CLM_apply]
  exact (physicalRestrictionL2_of_continuous _ _ hp).symm


end NLS.MKdV
