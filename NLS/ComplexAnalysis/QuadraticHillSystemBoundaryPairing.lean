import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import NLS.FunctionalAnalysis.LinearVolterra

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



private theorem integral_eq_sub_of_ac_of_restricted_derivative
    (f k : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hk : IntervalIntegrable k volume 0 1)
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f (k x) x) :
    (∫ x in (0 : ℝ)..1,k x)=f 1-f 0 := by
  apply integral_eq_sub_of_ac_of_ae_hasDerivAt hf hk
  rw [restrict_Ioc_eq_restrict_Icc] at hd
  have hh := (ae_restrict_iff' measurableSet_Icc).mp hd
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hh

theorem quadraticHillSystem_pairing_boundary_identity
    (a b : ℂ) (q : ℝ → ℂ)
    (g h r G H R : Curve ℂ)
    (hg : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend g) 0 1)
    (hh : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend h) 0 1)
    (hr : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend r) 0 1)
    (hG : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend G) 0 1)
    (hH : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend H) 0 1)
    (hR : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend R) 0 1)
    (hde : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend g) (NLS.LinearVolterra.extend h x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend h)
        (2*(q x-a)*NLS.LinearVolterra.extend g x+2*NLS.LinearVolterra.extend r x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend r) ((q x-a)*NLS.LinearVolterra.extend h x) x)
    (hdE : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend G) (NLS.LinearVolterra.extend H x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend H)
        (2*(q x-b)*NLS.LinearVolterra.extend G x+2*NLS.LinearVolterra.extend R x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend R) ((q x-b)*NLS.LinearVolterra.extend H x) x)
    : 4*(a-b)*(∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend g x*NLS.LinearVolterra.extend H x)=
      (2*NLS.LinearVolterra.extend r 1*NLS.LinearVolterra.extend G 1+
        2*NLS.LinearVolterra.extend g 1*NLS.LinearVolterra.extend R 1-
        NLS.LinearVolterra.extend h 1*NLS.LinearVolterra.extend H 1)-
      (2*NLS.LinearVolterra.extend r 0*NLS.LinearVolterra.extend G 0+
        2*NLS.LinearVolterra.extend g 0*NLS.LinearVolterra.extend R 0-
        NLS.LinearVolterra.extend h 0*NLS.LinearVolterra.extend H 0)+
      2*(a-b)*(NLS.LinearVolterra.extend g 1*NLS.LinearVolterra.extend G 1-
        NLS.LinearVolterra.extend g 0*NLS.LinearVolterra.extend G 0) := by
  let P (x : ℝ) := NLS.LinearVolterra.extend g x*NLS.LinearVolterra.extend H x
  let Q (x : ℝ) := NLS.LinearVolterra.extend h x*NLS.LinearVolterra.extend G x
  let K : ℝ → ℂ := (2 : ℂ) • (NLS.LinearVolterra.extend r*NLS.LinearVolterra.extend G)+
    (2 : ℂ) • (NLS.LinearVolterra.extend g*NLS.LinearVolterra.extend R)-
    NLS.LinearVolterra.extend h*NLS.LinearVolterra.extend H
  have hP : Continuous P := (continuous_extend g).mul (continuous_extend H)
  have hQ : Continuous Q := (continuous_extend h).mul (continuous_extend G)
  have hK : AbsolutelyContinuousOnInterval K 0 1 :=
    (((hr.smul hG).const_smul (2 : ℂ)).add ((hg.smul hR).const_smul (2 : ℂ))).sub (hh.smul hH)
  have hdk : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt K (2*(a-b)*(P x-Q x)) x := by
    filter_upwards [hde,hdE] with x hx hy
    convert! ((((hx.2.2.mul hy.1).const_mul (2 : ℂ)).add
      ((hx.1.mul hy.2.2).const_mul (2 : ℂ))).sub (hx.2.1.mul hy.2.1)) using 1
    dsimp only [P,Q]
    ring
  have hdp : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend g*NLS.LinearVolterra.extend G) (P x+Q x) x := by
    filter_upwards [hde,hdE] with x hx hy
    convert! hx.1.mul hy.1 using 1
    dsimp only [P,Q]
    ring
  have h1 := integral_eq_sub_of_ac_of_restricted_derivative K _ hK
    ((continuous_const.mul (hP.sub hQ)).intervalIntegrable 0 1) hdk
  have h2 := integral_eq_sub_of_ac_of_restricted_derivative _ _ (hg.smul hG)
    ((hP.add hQ).intervalIntegrable 0 1) hdp
  change (∫ x in (0 : ℝ)..1,2*(a-b)*(P x-Q x))=K 1-K 0 at h1
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hP.intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1)] at h1
  change (∫ x in (0 : ℝ)..1,P x+Q x)=
    NLS.LinearVolterra.extend g 1*NLS.LinearVolterra.extend G 1-
      NLS.LinearVolterra.extend g 0*NLS.LinearVolterra.extend G 0 at h2
  rw [intervalIntegral.integral_add (hP.intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1)] at h2
  dsimp only [K,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,Pi.add_apply,Pi.sub_apply] at h1
  change 4*(a-b)*(∫ x in (0 : ℝ)..1,P x)=_
  linear_combination h1+2*(a-b)*h2


/-- If the second quadratic solution has Dirichlet position and derivative
endpoints, only its quadratic momentum jump contributes to the pairing. -/
theorem quadraticHillSystem_pairing_dirichlet_boundary
    (a b : ℂ) (q : ℝ → ℂ)
    (g h r G H R : Curve ℂ)
    (hg : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend g) 0 1)
    (hh : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend h) 0 1)
    (hr : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend r) 0 1)
    (hG : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend G) 0 1)
    (hH : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend H) 0 1)
    (hR : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend R) 0 1)
    (hde : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend g) (NLS.LinearVolterra.extend h x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend h)
        (2*(q x-a)*NLS.LinearVolterra.extend g x+2*NLS.LinearVolterra.extend r x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend r) ((q x-a)*NLS.LinearVolterra.extend h x) x)
    (hdE : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend G) (NLS.LinearVolterra.extend H x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend H)
        (2*(q x-b)*NLS.LinearVolterra.extend G x+2*NLS.LinearVolterra.extend R x) x ∧
      HasDerivAt (NLS.LinearVolterra.extend R) ((q x-b)*NLS.LinearVolterra.extend H x) x)
    (hgper : NLS.LinearVolterra.extend g 1=NLS.LinearVolterra.extend g 0)
    (hG0 : NLS.LinearVolterra.extend G 0=0) (hG1 : NLS.LinearVolterra.extend G 1=0)
    (hH0 : NLS.LinearVolterra.extend H 0=0) (hH1 : NLS.LinearVolterra.extend H 1=0) :
    2*(a-b)*(∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend g x*NLS.LinearVolterra.extend H x)=
      NLS.LinearVolterra.extend g 0*(NLS.LinearVolterra.extend R 1-NLS.LinearVolterra.extend R 0) := by
  have hi := quadraticHillSystem_pairing_boundary_identity a b q g h r G H R
    hg hh hr hG hH hR hde hdE
  rw [hG0,hG1,hH0,hH1,hgper] at hi
  simp only [mul_zero,zero_add,sub_zero] at hi
  linear_combination hi/2

end NLS.ComplexAnalysis
