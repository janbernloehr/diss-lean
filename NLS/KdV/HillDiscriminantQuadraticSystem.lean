import NLS.KdV.HillDiscriminantGradientRegularity
import NLS.KdV.HillRoughScalarEquation

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



def hillDiscriminantQuadraticMomentumCurve (q : Coeff 2) (z : ℂ) : Curve ℂ :=
  let C := hillL2FrequencyStateCurve q z (1,0)
  let S := hillL2FrequencyStateCurve q z (0,1)
  let d := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp C
  let t := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp S
  (S ⟨1,by norm_num⟩).1 • d^2+
    ((S ⟨1,by norm_num⟩).2-(C ⟨1,by norm_num⟩).1) • (d*t)-
    (C ⟨1,by norm_num⟩).2 • t^2

private theorem spatial_formula (q : Coeff 2) (z : ℂ) :
    NLS.LinearVolterra.extend (hillDiscriminantGradientSpatialCurve q z)=fun x =>
      (2*(hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1)*
        ((NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).1*
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).2)+
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)*
        ((NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).2*
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).1+
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).1*
            (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).2)-
      (2*(hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2)*
        ((NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).1*
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).2) := rfl

private theorem momentum_formula (q : Coeff 2) (z : ℂ) :
    NLS.LinearVolterra.extend (hillDiscriminantQuadraticMomentumCurve q z)=fun x =>
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1*
        (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).2^2+
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)*
        ((NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).2*
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).2)-
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2*
        (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).2^2 := rfl

private theorem spatial_derivative_algebra (α β γ Q c d s t : ℂ) :
    (2*α)*(d*d+c*(Q*c))+β*((Q*c)*s+d*t+(d*t+c*(Q*s)))-(2*γ)*(t*t+s*(Q*s))=
      2*Q*(α*c^2+β*c*s-γ*s^2)+2*(α*d^2+β*(d*t)-γ*t^2) := by ring

private theorem momentum_derivative_algebra (α β γ Q c d s t : ℂ) :
    α*((2 : ℂ)*d^(2-1)*(Q*c))+β*((Q*c)*t+d*(Q*s))-γ*((2 : ℂ)*t^(2-1)*(Q*s))=
      Q*((2*α)*(c*d)+β*(d*s+c*t)-(2*γ)*(s*t)) := by
  simp only [show (2 : ℕ)-1=1 from rfl,pow_one]
  ring

/-- All components of the physical quadratic Hill system are absolutely
continuous at arbitrary complex L2 potentials. -/
theorem absolutelyContinuousOnInterval_hillDiscriminantQuadraticSystem (q : Coeff 2) (z : ℂ) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillDiscriminantGradientSpatialCurve q z)) 0 1 ∧
      AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillDiscriminantQuadraticMomentumCurve q z)) 0 1 := by
  have hc := absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_hillStateCurve q z (1,0))
    (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hd := absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_hillStateCurve q z (1,0))
    (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hs := absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_hillStateCurve q z (0,1))
    (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have ht := absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_hillStateCurve q z (0,1))
    (ContinuousLinearMap.snd ℝ ℂ ℂ)
  constructor
  · exact (((hc.smul hd).const_smul (2*(hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1)).add
      (((hd.smul hs).add (hc.smul ht)).const_smul ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1))).sub
      ((hs.smul ht).const_smul (2*(hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2))
  · have hh := (((hd.smul hd).const_smul (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1).add
      ((hd.smul ht).const_smul ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1))).sub
      ((ht.smul ht).const_smul (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2)
    convert! hh using 1
    funext x
    rw [momentum_formula]
    simp only [Pi.sub_apply,Pi.add_apply,smul_eq_mul,ContinuousLinearMap.coe_snd',pow_two,Pi.mul_apply]

/-- The actual trace cotangent, its spatial derivative and the quadratic
momentum satisfy the rough first-order Hill system with energy z^2. -/
theorem ae_hasDerivAt_hillDiscriminantQuadraticSystem (q : Coeff 2) (z : ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z))
        (NLS.LinearVolterra.extend (hillDiscriminantGradientSpatialCurve q z) x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend (hillDiscriminantGradientSpatialCurve q z))
        (2*(hillL2ScalarRepresentative q x-z^2)*NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z) x+
          2*NLS.LinearVolterra.extend (hillDiscriminantQuadraticMomentumCurve q z) x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend (hillDiscriminantQuadraticMomentumCurve q z))
        ((hillL2ScalarRepresentative q x-z^2)*NLS.LinearVolterra.extend (hillDiscriminantGradientSpatialCurve q z) x) x := by
  filter_upwards [ae_hasDerivAt_hillDiscriminantGradientCurve q z,
    ae_hasDerivAt_hillL2FrequencyStateCurve_fst q z (1,0),
    ae_hasDerivAt_hillL2FrequencyStateCurve_snd q z (1,0),
    ae_hasDerivAt_hillL2FrequencyStateCurve_fst q z (0,1),
    ae_hasDerivAt_hillL2FrequencyStateCurve_snd q z (0,1)] with x hg hc hd hs ht
  refine ⟨hg,?_,?_⟩
  · rw [spatial_formula]
    have h1 := (hc.mul hd).const_mul (2*(hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1)
    have h2 := ((hd.mul hs).add (hc.mul ht)).const_mul
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)
    have h3 := (hs.mul ht).const_mul (2*(hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2)
    have hh := (h1.add h2).sub h3
    convert! hh using 1
    dsimp only [NLS.LinearVolterra.extend]
    rw [hillDiscriminantGradientCurve_eq_scalar_polynomial]
    dsimp only [hillDiscriminantQuadraticMomentumCurve,ContinuousMap.add_apply,ContinuousMap.sub_apply,
      ContinuousMap.smul_apply,ContinuousMap.pow_apply,ContinuousMap.mul_apply,ContinuousMap.comp_apply,smul_eq_mul]
    exact (spatial_derivative_algebra
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-(hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2
      (hillL2ScalarRepresentative q x-z^2)
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).1
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).2
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).1
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).2).symm
  · rw [momentum_formula]
    have h1 := (hd.pow 2).const_mul (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1
    have h2 := (hd.mul ht).const_mul
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)
    have h3 := (ht.pow 2).const_mul (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2
    have hh := (h1.add h2).sub h3
    convert! hh using 1
    rw [spatial_formula]
    exact (momentum_derivative_algebra
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-(hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2
      (hillL2ScalarRepresentative q x-z^2)
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).1
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).2
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).1
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).2).symm

private theorem momentum_endpoint_algebra (C S D T : ℂ) (h : C*T-S*D=1) :
    S*D^2+(T-C)*(D*T)-D*T^2= -D := by
  linear_combination -D*h

theorem hillDiscriminantQuadraticMomentumCurve_endpoints (q : Coeff 2) (z : ℂ) :
    hillDiscriminantQuadraticMomentumCurve q z ⟨0,by norm_num⟩=
      -(hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2 ∧
    hillDiscriminantQuadraticMomentumCurve q z ⟨1,by norm_num⟩=
      -(hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2 := by
  constructor
  · change (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1*
        (hillL2FrequencyStateCurve q z (1,0) ⟨0,by norm_num⟩).2^2+
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)*
        ((hillL2FrequencyStateCurve q z (1,0) ⟨0,by norm_num⟩).2*
          (hillL2FrequencyStateCurve q z (0,1) ⟨0,by norm_num⟩).2)-
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2*
        (hillL2FrequencyStateCurve q z (0,1) ⟨0,by norm_num⟩).2^2=_
    rw [hillL2FrequencyStateCurve_zero,hillL2FrequencyStateCurve_zero]
    ring
  · exact momentum_endpoint_algebra _ _ _ _ (hillL2FrequencyStateCurve_wronskian q z ⟨1,by norm_num⟩)

end NLS.KdV
