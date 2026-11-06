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

/-- Distinct-energy periodic quadratic Hill systems have zero Gardner
pairing. The rough potential enters only in the a.e. first-order system. -/
theorem quadraticHillSystem_pairing_eq_zero
    (a b : ℂ) (hab : a≠b) (q : ℝ → ℂ)
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
    (hgper : g ⟨1,by norm_num⟩=g ⟨0,by norm_num⟩)
    (hhper : h ⟨1,by norm_num⟩=h ⟨0,by norm_num⟩)
    (hrper : r ⟨1,by norm_num⟩=r ⟨0,by norm_num⟩)
    (hGper : G ⟨1,by norm_num⟩=G ⟨0,by norm_num⟩)
    (hHper : H ⟨1,by norm_num⟩=H ⟨0,by norm_num⟩)
    (hRper : R ⟨1,by norm_num⟩=R ⟨0,by norm_num⟩) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend g x*NLS.LinearVolterra.extend H x)=0 := by
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
  have hKper : K 1=K 0 := by
    dsimp only [K,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,NLS.LinearVolterra.extend]
    rw [projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num)]
    rw [hgper,hhper,hrper,hGper,hHper,hRper]
  change (∫ x in (0 : ℝ)..1,2*(a-b)*(P x-Q x))=K 1-K 0 at h1
  rw [hKper,sub_self,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hP.intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1)] at h1
  have hproductper : (NLS.LinearVolterra.extend g*NLS.LinearVolterra.extend G) 1=
      (NLS.LinearVolterra.extend g*NLS.LinearVolterra.extend G) 0 := by
    dsimp only [Pi.mul_apply,NLS.LinearVolterra.extend]
    rw [projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num)]
    rw [hgper,hGper]
  change (∫ x in (0 : ℝ)..1,P x+Q x)=
    (NLS.LinearVolterra.extend g*NLS.LinearVolterra.extend G) 1-
      (NLS.LinearVolterra.extend g*NLS.LinearVolterra.extend G) 0 at h2
  rw [hproductper,sub_self,intervalIntegral.integral_add (hP.intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1)] at h2
  have heq : (∫ x in (0 : ℝ)..1,P x)-(∫ x in (0 : ℝ)..1,Q x)=0 :=
    (mul_eq_zero.mp h1).resolve_left (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hab))
  change (∫ x in (0 : ℝ)..1,P x)=0
  linear_combination (heq+h2)/2

end NLS.ComplexAnalysis
