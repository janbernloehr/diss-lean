import NLS.KdV.HillL2GreenIdentity
import NLS.ZakharovShabat.L2SolutionNonvanishing
import NLS.ZakharovShabat.L2SolutionDifferentialEquation

/-! # Reality of every Dirichlet zero of a real rough L2 Hill potential. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate ENNReal
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2FrequencyStateCurve_ne_zero (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ)
    (hv : v≠0) (t : Icc (0 : ℝ) 1) : hillL2FrequencyStateCurve q z v t≠0 := by
  intro h
  have he := (constantUpperStateMap_injective z) (h.trans (map_zero _).symm)
  apply l2SolutionCurve_ne_zero (physicalRestrictionL2 (hillFirstOrderPotential q)) z
    (constantUpperInitialVector z v) ?_ t he
  intro hh
  apply hv
  rw [← constantUpperStateMap_initialVector z v,hh,map_zero]


theorem hillFirstOrder_upper_eq_neg_one_ae (q : Coeff 2) :
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      (intervalL2Representative (physicalRestrictionL2 (hillFirstOrderPotential q)) s).1=-1 := by
  have hc := hillFirstOrder_continuous_compatibility (0 : C(AddCircle (2 : ℝ),ℂ))
  filter_upwards [physicalRestrictionL2_representative (hillFirstOrderPotential q),hc] with s hs ht
  rw [hs]
  have he : (physicalBase (hillFirstOrderPotential q) s).1 =
      (physicalBase (hillFirstOrderPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients (0 : C(AddCircle (2 : ℝ),ℂ))))) s).1 := rfl
  rw [he]
  have hh := congrArg Prod.fst ht
  simpa only [NLS.LinearVolterra.extend,constantUpperPotential_apply] using hh

theorem ae_hasDerivAt_hillL2FrequencyStateCurve_fst (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) :
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun x : ℝ => (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z v) x).1)
        (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z v) s).2 s := by
  filter_upwards [ae_hasDerivAt_l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z
      (constantUpperInitialVector z v),hillFirstOrder_upper_eq_neg_one_ae q] with s hs hu
  have hd : HasDerivAt (fun x : ℝ => (NLS.LinearVolterra.extend
      (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v)) x).1)
      ((classicalODECoefficient (intervalL2Representative (physicalRestrictionL2 (hillFirstOrderPotential q)) s) z
        (NLS.LinearVolterra.extend (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v)) s)).1) s := by
    simpa using! HasFDerivAt.hasDerivAt hs.fst
  simp only [classicalODECoefficient_apply,hu] at hd
  convert! hd using 1
  dsimp only [NLS.LinearVolterra.extend,hillL2FrequencyStateCurve,ContinuousMap.comp_apply,
    constantUpperStateMap_apply,ContinuousMap.coe_mk]
  ring

theorem hillL2FrequencyStateCurve_mass_pos (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) (hv : v≠0) :
    0<scalarStateMass (hillL2FrequencyStateCurve q z v) :=
  scalarStateMass_pos_of_first_derivative _ (hillL2FrequencyStateCurve_ne_zero q z v hv)
    (ae_hasDerivAt_hillL2FrequencyStateCurve_fst q z v)

theorem hillL2DirichletCharacteristic_zero_real (q : Coeff 2) (hq : IsRealHillPotential q) (energy : ℂ)
    (hz : hillL2DirichletCharacteristic q energy=0) : energy.im=0 := by
  let z := Complex.sqrt energy
  have hs : z^2=energy := NLS.ComplexAnalysis.complex_sqrt_sq _
  have hzero : (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1=0 := by
    simpa only [hillL2DirichletCharacteristic,hillL2FrequencyDirichlet,
      hillL2FrequencyStateCurve_apply,constantUpperStateMap_apply,constantUpperInitialVector,
      mul_zero,mul_one,sub_zero] using! hz
  have hG := hillL2FrequencyStateCurve_green_im q hq z (0,1)
  rw [hs] at hG
  simp only [hzero,map_zero,zero_mul,zero_im,sub_self] at hG
  have hm := hillL2FrequencyStateCurve_mass_pos q z (0,1)
    (by intro h; have hh := congrArg Prod.snd h; norm_num at hh)
  exact neg_eq_zero.mp ((mul_eq_zero.mp hG).resolve_right hm.ne')

end NLS.KdV
