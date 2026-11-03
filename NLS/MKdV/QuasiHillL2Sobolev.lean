import NLS.MKdV.QuasiHillL2Energy
import NLS.MKdV.SobolevMiuraPrimitive

/-! The energy-affine L2 realization agrees with the independent physical
quasi-Hill IVP on every original H1 Miura input, with no representation
compatibility hypothesis supplied by the caller. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat
namespace NLS.MKdV

/-- The energy-dependent source has exactly the physical continuous
representative of the original H1 input. -/
theorem sourcePhysicalL2_quasiHillEnergySource_scalarInclusion
    (a : ScalarDomain 2) (lambda : ℂ) :
    sourcePhysicalL2 (quasiHillEnergySource (scalarInclusion a) lambda) =
      continuousPotentialL2Class (quasiHillEnergyCurve (periodOneMiuraCurve a) lambda) := by
  let c := (lambda-1)/2
  let f := (-I) • a+scalarMode 0 c
  let g := I • a+scalarMode 0 c
  let D : Domain 2 := (Coeff.periodDoubleSobolev f,Coeff.periodDoubleSobolev g)
  have hsource : quasiHillEnergySource (scalarInclusion a) lambda = sobolevSourceInclusion (f,g) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext n
    · change ((-I) • scalarInclusion a+lp.single 2 0 c : Coeff 2) n+0 = (sobolevSourceInclusion (f,g)).fst n
      simp only [sobolevSourceInclusion_fst,f,WeightedCoeff.add_val,WeightedCoeff.smul_val,
        scalarMode_apply,lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
        scalarInclusion_apply,lp.single_apply,Pi.single_apply,add_zero]
    · change 0+(I • scalarInclusion a+lp.single 2 0 c : Coeff 2) n = (sobolevSourceInclusion (f,g)).snd n
      simp only [sobolevSourceInclusion_snd,g,WeightedCoeff.add_val,WeightedCoeff.smul_val,
        scalarMode_apply,lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
        scalarInclusion_apply,lp.single_apply,Pi.single_apply,zero_add]
  have hper : periodOnePotential (sobolevSourceInclusion (f,g)) = domainInclusion D := by
    apply Prod.ext <;> ext n <;>
      simp [periodOnePotential_apply,domainInclusion_apply,D,scalarInclusion_apply,
        Coeff.periodDoubleSobolev_apply,sobolevSourceInclusion]
  have hlin (d : ℂ) : periodOneMiuraCurve (d • a+scalarMode 0 c) =
      d • periodOneMiuraCurve a+ContinuousMap.const _ c := by
    rw [← periodOneMiuraCurveCLM_apply,map_add,map_smul]
    simp only [periodOneMiuraCurveCLM_apply]
    congr 1
    apply ContinuousMap.ext
    intro t
    rw [periodOneMiuraCurve_apply]
    simpa [wave] using periodOneSobolevSynthesis_scalarMode (0:ℤ) c (t:ℝ)
  have hcurve : physicalDomainCurve D = quasiHillEnergyCurve (periodOneMiuraCurve a) lambda := by
    apply ContinuousMap.ext
    intro t
    change (periodOneMiuraCurve f t,periodOneMiuraCurve g t) =
      (-I*periodOneMiuraCurve a t+c,I*periodOneMiuraCurve a t+c)
    simp only [f,g,hlin,ContinuousMap.add_apply,ContinuousMap.smul_apply,
      ContinuousMap.const_apply,smul_eq_mul]
  change physicalRestrictionL2 (periodOnePotential _) = _
  rw [hsource]
  apply physicalRestrictionL2_of_continuous
  rw [hper,← hcurve]
  exact physicalBase_eq_extend_physicalDomainCurve D

/-- Full scalar solution agreement on every original complex H1 Miura input. -/
theorem quasiHillL2SolutionCurve_scalarInclusion (a : ScalarDomain 2) (lambda : ℂ)
    (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    quasiHillL2SolutionCurve (scalarInclusion a) lambda v t =
      quasiHillSolution (periodOneMiuraCurve a) lambda v t :=
  quasiHillL2SolutionCurve_eq_continuous _ _ _
    (sourcePhysicalL2_quasiHillEnergySource_scalarInclusion a lambda) v t

/-- Exact Dirichlet normalization on the dense original H1 subspace. -/
theorem quasiHillL2Dirichlet_scalarInclusion (a : ScalarDomain 2) (lambda : ℂ) :
    quasiHillL2Dirichlet (scalarInclusion a) lambda = quasiHillDirichlet (periodOneMiuraCurve a) lambda :=
  quasiHillL2Dirichlet_eq_continuous _ _ _
    (sourcePhysicalL2_quasiHillEnergySource_scalarInclusion a lambda)

end NLS.MKdV
