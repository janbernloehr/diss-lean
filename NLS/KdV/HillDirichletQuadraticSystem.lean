import NLS.KdV.HillDiscriminantQuadraticSystem
import NLS.KdV.HillDirichletGardnerBrackets

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



def hillDirichletQuadraticMomentumCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) : Curve ℂ :=
  (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹ •
    (((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp (hillDirichletStateCurve q n hn))^2)

theorem absolutelyContinuousOnInterval_hillDirichletQuadraticSystem
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q n hn)) 0 1 ∧
      AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillDirichletQuadraticMomentumCurve q n hn)) 0 1 := by
  have hs := absolutelyContinuousOnInterval_hillStateCurve (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)
  have hp := absolutelyContinuousOnInterval_clm hs (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hd := absolutelyContinuousOnInterval_clm hs (ContinuousLinearMap.snd ℝ ℂ ℂ)
  constructor
  · exact (hp.smul hd).const_smul (2/(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ))
  · convert! (hd.smul hd).const_smul ((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹) using 1
    funext x
    change (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
      (NLS.LinearVolterra.extend (hillDirichletStateCurve q n hn) x).2^2=_
    dsimp only [hillDirichletStateCurve,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,ContinuousLinearMap.coe_snd']
    ring

theorem ae_hasDerivAt_hillDirichletQuadraticSystem
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn))
        (NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q n hn) x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q n hn))
        (2*(hillL2ScalarRepresentative (SpectralWeight.one.toCoeff q.val) x-
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))*
          NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn) x+
          2*NLS.LinearVolterra.extend (hillDirichletQuadraticMomentumCurve q n hn) x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend (hillDirichletQuadraticMomentumCurve q n hn))
        ((hillL2ScalarRepresentative (SpectralWeight.one.toCoeff q.val) x-
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))*
          NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q n hn) x) x := by
  filter_upwards [ae_hasDerivAt_hillDirichletGradientCurve q n hn,
    ae_hasDerivAt_hillL2FrequencyStateCurve_fst (SpectralWeight.one.toCoeff q.val)
      (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1),
    ae_hasDerivAt_hillL2FrequencyStateCurve_snd (SpectralWeight.one.toCoeff q.val)
      (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)] with x hg hs hd
  rw [complex_sqrt_sq] at hd
  refine ⟨hg,?_,?_⟩
  · have hh := (hs.mul hd).const_mul (2/(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ))
    convert! hh using 1
    change 2*(_-_)*((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
      (NLS.LinearVolterra.extend (hillDirichletStateCurve q n hn) x).1^2)+
      2*((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
        (NLS.LinearVolterra.extend (hillDirichletStateCurve q n hn) x).2^2)=_
    simp only [div_eq_mul_inv]
    dsimp only [hillDirichletStateCurve,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,ContinuousLinearMap.coe_snd']
    ring
  · have hh := (hd.pow 2).const_mul ((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹)
    convert! hh using 1
    change (_-_)*((2/(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ))*
      ((NLS.LinearVolterra.extend (hillDirichletStateCurve q n hn) x).1*
        (NLS.LinearVolterra.extend (hillDirichletStateCurve q n hn) x).2))=_
    simp only [show (2 : ℕ)-1=1 from rfl,pow_one,div_eq_mul_inv]
    dsimp only [hillDirichletStateCurve,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,ContinuousLinearMap.coe_snd']
    ring

theorem hillDirichletGradientSpatialCurve_endpoints
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    hillDirichletGradientSpatialCurve q n hn ⟨0,by norm_num⟩=0 ∧
      hillDirichletGradientSpatialCurve q n hn ⟨1,by norm_num⟩=0 := by
  have h1 : (hillDirichletStateCurve q n hn ⟨1,by norm_num⟩).1=0 :=
    hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
  constructor
  · change (2/(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ))*
      ((hillDirichletStateCurve q n hn ⟨0,by norm_num⟩).1*
        (hillDirichletStateCurve q n hn ⟨0,by norm_num⟩).2)=0
    dsimp only [hillDirichletStateCurve]
    rw [hillL2FrequencyStateCurve_zero]
    dsimp only [hillDirichletStateCurve,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,ContinuousLinearMap.coe_snd']
    ring
  · change (2/(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ))*
      ((hillDirichletStateCurve q n hn ⟨1,by norm_num⟩).1*
        (hillDirichletStateCurve q n hn ⟨1,by norm_num⟩).2)=0
    rw [h1,zero_mul,mul_zero]

theorem hillDirichletQuadraticMomentumCurve_endpoints
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    hillDirichletQuadraticMomentumCurve q n hn ⟨0,by norm_num⟩=
      (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹ ∧
      hillDirichletQuadraticMomentumCurve q n hn ⟨1,by norm_num⟩=
        (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
          (hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
            (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2 := by
  constructor
  · change (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
      (hillDirichletStateCurve q n hn ⟨0,by norm_num⟩).2^2=_
    dsimp only [hillDirichletStateCurve]
    rw [hillL2FrequencyStateCurve_zero]
    dsimp only [hillDirichletStateCurve,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,ContinuousLinearMap.coe_snd']
    ring
  · rfl

end NLS.KdV
