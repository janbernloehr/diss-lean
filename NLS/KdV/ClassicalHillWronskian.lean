import NLS.KdV.ClassicalHillGreen

/-! Actual scalar Hill cross-energy Lagrange identities and the
normalized fundamental Wronskian, for every complex continuous potential. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.KdV

def classicalHillWronskian (q : Curve ℂ) (μ ν : ℂ) (v w : ℂ × ℂ) (x : ℝ) : ℂ :=
  (classicalHillFlow q μ v x).1*(classicalHillFlow q ν w x).2-
    (classicalHillFlow q μ v x).2*(classicalHillFlow q ν w x).1

theorem continuous_classicalHillWronskian (q : Curve ℂ) (μ ν : ℂ) (v w : ℂ × ℂ) :
    Continuous (classicalHillWronskian q μ ν v w) :=
  ((continuous_classicalHillFlow q μ v).fst.mul (continuous_classicalHillFlow q ν w).snd).sub
    ((continuous_classicalHillFlow q μ v).snd.mul (continuous_classicalHillFlow q ν w).fst)

theorem hasDerivAt_classicalHillWronskian (q : Curve ℂ) (μ ν : ℂ) (v w : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillWronskian q μ ν v w)
      ((μ-ν)*(classicalHillFlow q μ v t).1*(classicalHillFlow q ν w t).1) t := by
  have hv := hasDerivAt_classicalHillFlow q μ v t
  have hw := hasDerivAt_classicalHillFlow q ν w t
  have hf : HasDerivAt (fun x => (classicalHillFlow q μ v x).1) (classicalHillFlow q μ v t).2 t := by
    simpa using! HasFDerivAt.hasDerivAt hv.fst
  have hg : HasDerivAt (fun x => (classicalHillFlow q μ v x).2)
      ((q t-μ)*(classicalHillFlow q μ v t).1) t := by simpa using! HasFDerivAt.hasDerivAt hv.snd
  have hh : HasDerivAt (fun x => (classicalHillFlow q ν w x).1) (classicalHillFlow q ν w t).2 t := by
    simpa using! HasFDerivAt.hasDerivAt hw.fst
  have hk : HasDerivAt (fun x => (classicalHillFlow q ν w x).2)
      ((q t-ν)*(classicalHillFlow q ν w t).1) t := by simpa using! HasFDerivAt.hasDerivAt hw.snd
  convert (hf.mul hk).sub (hg.mul hh) using 1 <;> first | rfl | ring

theorem classicalHillWronskian_integral (q : Curve ℂ) (μ ν : ℂ) (v w : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..t.val, (μ-ν)*(classicalHillFlow q μ v s).1*(classicalHillFlow q ν w s).1)=
      classicalHillWronskian q μ ν v w t-(v.1*w.2-v.2*w.1) := by
  have hc : Continuous (fun s : ℝ => (μ-ν)*(classicalHillFlow q μ v s).1*(classicalHillFlow q ν w s).1) :=
    (continuous_const.mul (continuous_classicalHillFlow q μ v).fst).mul (continuous_classicalHillFlow q ν w).fst
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (continuous_classicalHillWronskian q μ ν v w).continuousOn
    (fun x hx => hasDerivAt_classicalHillWronskian q μ ν v w
      ⟨x,hx.1.le,hx.2.le.trans t.property.2⟩) (hc.intervalIntegrable 0 t)
  simpa only [classicalHillWronskian,classicalHillFlow_zero] using h

theorem classicalHillWronskian_same_energy (q : Curve ℂ) (μ : ℂ) (v w : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) : classicalHillWronskian q μ μ v w t=v.1*w.2-v.2*w.1 := by
  have h := classicalHillWronskian_integral q μ μ v w t
  simp only [sub_self,zero_mul,intervalIntegral.integral_zero] at h
  exact sub_eq_zero.mp h.symm

theorem classicalHillFundamental_wronskian (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    (classicalHillFlow q μ (1,0) t).1*(classicalHillFlow q μ (0,1) t).2-
      (classicalHillFlow q μ (1,0) t).2*(classicalHillFlow q μ (0,1) t).1=1 := by
  simpa only [classicalHillWronskian,mul_one,mul_zero,sub_zero] using
    classicalHillWronskian_same_energy q μ (1,0) (0,1) t

end NLS.KdV
