import NLS.KdV.HillDiscriminantGradient
import NLS.KdV.HillDirichletGradientH1

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



def hillDiscriminantGradientSpatialCurve (q : Coeff 2) (z : ℂ) : Curve ℂ :=
  let C := hillL2FrequencyStateCurve q z (1,0)
  let S := hillL2FrequencyStateCurve q z (0,1)
  let c := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp C
  let d := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp C
  let s := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp S
  let t := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp S
  (2*(S ⟨1,by norm_num⟩).1) • (c*d)+
    ((S ⟨1,by norm_num⟩).2-(C ⟨1,by norm_num⟩).1) • (d*s+c*t)-
    (2*(C ⟨1,by norm_num⟩).2) • (s*t)

private theorem extend_trace_gradient (q : Coeff 2) (z : ℂ) (x : ℝ) :
    NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z) x=
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1*
        (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).1^2+
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)*
        (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).1*
        (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).1-
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2*
        (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).1^2 :=
  hillDiscriminantGradientCurve_eq_scalar_polynomial q z (projIcc 0 1 (by norm_num) x)

/-- The scalar trace cotangent is absolutely continuous at arbitrary
complex L2 Hill potentials. -/
theorem absolutelyContinuousOnInterval_hillDiscriminantGradientCurve (q : Coeff 2) (z : ℂ) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z)) 0 1 := by
  have hC := absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_hillStateCurve q z (1,0))
    (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hS := absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_hillStateCurve q z (0,1))
    (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hh := (((hC.smul hC).const_smul (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1).add
    ((hC.smul hS).const_smul ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1))).sub
    ((hS.smul hS).const_smul (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2)
  convert! hh using 1
  funext x
  change NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z) x=
    (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1*
      ((NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).1*
        (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).1)+
    ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)*
      ((NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (1,0)) x).1*
        (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).1)-
    (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2*
      ((NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).1*
        (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).1)
  simpa only [pow_two,mul_assoc] using extend_trace_gradient q z x

/-- The genuine spatial derivative uses only the continuous scalar
state and derivative components, without differentiating the rough potential. -/
theorem ae_hasDerivAt_hillDiscriminantGradientCurve (q : Coeff 2) (z : ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z))
        (NLS.LinearVolterra.extend (hillDiscriminantGradientSpatialCurve q z) x) x := by
  have hC := ae_hasDerivAt_hillL2FrequencyStateCurve_fst q z (1,0)
  have hS := ae_hasDerivAt_hillL2FrequencyStateCurve_fst q z (0,1)
  filter_upwards [hC,hS] with x hc hs
  have hh := (((hc.pow 2).const_mul (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1).add
    ((hc.mul hs).const_mul ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1))).sub
    ((hs.pow 2).const_mul (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2)
  convert! hh using 1
  · funext y
    simpa only [Pi.sub_apply,Pi.add_apply,Pi.pow_apply,Pi.mul_apply,mul_assoc] using extend_trace_gradient q z y
  · change (2*(hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1)*
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
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).2)=_
    simp only [show (2 : ℕ)-1=1 from rfl,pow_one]
    ring

theorem hillDiscriminantGradient_H1 (q : Coeff 2) (z : ℂ) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z)) 0 1 ∧
      MemLp (NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      MemLp (deriv (NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hmem (w : Curve ℂ) : MemLp (NLS.LinearVolterra.extend w) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm (continuous_extend w).aestronglyMeasurable).mpr
      (((continuous_extend w).norm.pow 2).intervalIntegrable 0 1).1
  refine ⟨absolutelyContinuousOnInterval_hillDiscriminantGradientCurve q z,hmem _,?_⟩
  apply (hmem (hillDiscriminantGradientSpatialCurve q z)).ae_eq
  filter_upwards [ae_hasDerivAt_hillDiscriminantGradientCurve q z] with x hx
  exact hx.deriv.symm

private theorem trace_gradient_endpoint_algebra (C S D T : ℂ) (h : C*T-S*D=1) :
    S*C^2+(T-C)*C*S-D*S^2=S := by
  linear_combination S*h

private theorem trace_gradient_spatial_endpoint_algebra (C S D T : ℂ) (h : C*T-S*D=1) :
    (2*S)*(C*D)+(T-C)*(D*S+C*T)-(2*D)*(S*T)=T-C := by
  linear_combination (T-C)*h

/-- The endpoint values of the physical trace cotangent agree by the
actual scalar Wronskian, without a smoothness assumption. -/
theorem hillDiscriminantGradientCurve_endpoints (q : Coeff 2) (z : ℂ) :
    hillDiscriminantGradientCurve q z ⟨0,by norm_num⟩=
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1 ∧
    hillDiscriminantGradientCurve q z ⟨1,by norm_num⟩=
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1 := by
  constructor
  · rw [hillDiscriminantGradientCurve_eq_scalar_polynomial]
    rw [hillL2FrequencyStateCurve_zero,hillL2FrequencyStateCurve_zero]
    ring
  · rw [hillDiscriminantGradientCurve_eq_scalar_polynomial]
    exact trace_gradient_endpoint_algebra _ _ _ _ (hillL2FrequencyStateCurve_wronskian q z ⟨1,by norm_num⟩)

theorem hillDiscriminantGradientSpatialCurve_endpoints (q : Coeff 2) (z : ℂ) :
    hillDiscriminantGradientSpatialCurve q z ⟨0,by norm_num⟩=
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1 ∧
    hillDiscriminantGradientSpatialCurve q z ⟨1,by norm_num⟩=
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1 := by
  constructor
  · change (2*(hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1)*
        ((hillL2FrequencyStateCurve q z (1,0) ⟨0,by norm_num⟩).1*
          (hillL2FrequencyStateCurve q z (1,0) ⟨0,by norm_num⟩).2)+
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)*
        ((hillL2FrequencyStateCurve q z (1,0) ⟨0,by norm_num⟩).2*
          (hillL2FrequencyStateCurve q z (0,1) ⟨0,by norm_num⟩).1+
          (hillL2FrequencyStateCurve q z (1,0) ⟨0,by norm_num⟩).1*
            (hillL2FrequencyStateCurve q z (0,1) ⟨0,by norm_num⟩).2)-
      (2*(hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2)*
        ((hillL2FrequencyStateCurve q z (0,1) ⟨0,by norm_num⟩).1*
          (hillL2FrequencyStateCurve q z (0,1) ⟨0,by norm_num⟩).2)=_
    rw [hillL2FrequencyStateCurve_zero,hillL2FrequencyStateCurve_zero]
    ring
  · exact trace_gradient_spatial_endpoint_algebra _ _ _ _ (hillL2FrequencyStateCurve_wronskian q z ⟨1,by norm_num⟩)

end NLS.KdV
