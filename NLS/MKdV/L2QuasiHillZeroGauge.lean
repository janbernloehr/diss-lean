import NLS.FunctionalAnalysis.PeriodicScalarACMean
import NLS.FunctionalAnalysis.UnitIntervalPrimitive
import NLS.MKdV.L2QuasiHillWeakReconstruction
import NLS.MKdV.L2QuasiHillMultipliers

/-! # A positive periodic zero-energy state for a real mean-zero L2 profile

The actual gauge is the exponential of the actual L1 primitive. No
pointwise coefficient regularity or ground-state solution is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis
namespace NLS.MKdV

theorem exists_positive_periodic_L2_gauge (u : IntervalL2) (hu : star u = u)
    (hm : (∫ x in (0 : ℝ)..1, u x) = 0) :
    ∃ y : Curve ℂ, AbsolutelyContinuousOnInterval (extend y) 0 1 ∧
      MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      extend y 0 = 1 ∧ extend y 1 = 1 ∧
      (∀ t : Icc (0 : ℝ) 1, 0 < (y t).re ∧ (y t).im = 0) ∧
      ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend y) (u x*extend y x) x := by
  have hi : IntervalIntegrable (fun x => u x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((Lp.memLp u).integrable (by norm_num))
  let P := unitIntervalPrimitiveCurve (fun x => u x) hi
  let y : Curve ℂ := ⟨fun t => (Real.exp ((P t).re) : ℂ),
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_re.comp P.continuous))⟩
  have heq (x : ℝ) : extend y x = (Real.exp ((extend P x).re) : ℂ) := rfl
  have hPa := absolutelyContinuous_unitIntervalPrimitiveCurve (fun x => u x) hi
  have hRa := absolutelyContinuousOnInterval_clm hPa Complex.reCLM
  have hEa := absolutelyContinuous_real_exp hRa
  have hya : AbsolutelyContinuousOnInterval (extend y) 0 1 :=
    absolutelyContinuousOnInterval_clm hEa Complex.ofRealCLM
  have hreal : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), u x = ((u x).re : ℂ) := by
    have hs := Lp.coeFn_star u
    rw [hu] at hs
    filter_upwards [hs] with x hx
    have him := congrArg Complex.im hx
    change (u x).im = -(u x).im at him
    apply Complex.ext
    · rfl
    · simp only [ofReal_im]
      linarith
  have hyd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend y) (u x*extend y x) x := by
    filter_upwards [ae_hasDerivAt_unitIntervalPrimitiveCurve (fun x => u x) hi,hreal] with x hx hr
    have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hx
    have hExp := hRe.exp.ofReal_comp
    change HasDerivAt (extend y) ((Real.exp ((extend P x).re)*(u x).re : ℝ) : ℂ) x at hExp
    convert hExp using 1
    rw [heq,hr]
    push_cast
    simp only [ofReal_re]
    ring
  have hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_congr_ae (hyd.mono (fun _ hx => hx.deriv))).mpr (memLp_intervalL2_mul_curve u y)
  refine ⟨y,hya,hy₂,?_,?_,?_,hyd⟩
  · rw [heq,unitIntervalPrimitiveCurve_zero]
    norm_num
  · rw [heq,unitIntervalPrimitiveCurve_one,hm]
    norm_num
  · intro t
    exact ⟨Real.exp_pos _,rfl⟩

/-- The ACTUAL rough quasi-Hill monodromy has trace two at zero energy
for every real mean-zero L2 profile, including nonsmooth profiles. -/
theorem l2QuasiHillDiscriminant_zero_eq_two_of_real_meanZero
    (u : IntervalL2) (hu : star u = u) (hm : (∫ x in (0 : ℝ)..1, u x) = 0) :
    l2QuasiHillDiscriminant u 0 = 2 := by
  obtain ⟨y,hy,_hy₂,hy0,hy1,_hpos,hd⟩ := exists_positive_periodic_L2_gauge u hu hm
  have hezero : NLS.LinearVolterra.extend (0 : Curve ℂ) = (fun _ : ℝ => (0 : ℂ)) := rfl
  have hzero : AbsolutelyContinuousOnInterval (extend (0 : Curve ℂ)) 0 1 := by
    simpa only [hezero] using
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (0 : ℂ))).contDiffOn.absolutelyContinuousOnInterval
  have hstate := l2QuasiHillSolution_eq_of_AC_state u 0 y 0 hy hzero (by
    filter_upwards [hd] with x hx
    refine ⟨?_,?_⟩
    · simpa only [hezero,add_zero] using hx
    · simpa only [hezero,neg_zero,zero_mul,mul_zero,sub_zero] using hasDerivAt_const x (0 : ℂ))
  have h00 : extend (0 : Curve ℂ) 0 = 0 := rfl
  rw [hy0,h00] at hstate
  apply (l2QuasiHillDiscriminant_eq_two_iff u 0).mpr
  refine ⟨(1,0),by simp,?_⟩
  rw [←hstate]
  apply Prod.ext
  · exact (extend_coe y ⟨1,by constructor <;> norm_num⟩).symm.trans hy1
  · rfl

end NLS.MKdV
