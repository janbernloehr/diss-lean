import NLS.KdV.ClassicalHillWronskian
import NLS.KdV.ClassicalHillPotentialVariation

/-! The ACTUAL zero-initial potential variation has a Wronskian whose
derivative is the actual forcing product. No free-potential assumption is used. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.KdV

def classicalHillVariationWronskian (q h : Curve ℂ) (μ : ℂ) (v w : ℂ × ℂ) (x : ℝ) : ℂ :=
  (classicalHillFlow q μ v x).1*(classicalHillPotentialVariation q h μ w x).2-
    (classicalHillFlow q μ v x).2*(classicalHillPotentialVariation q h μ w x).1

theorem continuous_classicalHillVariationWronskian (q h : Curve ℂ) (μ : ℂ) (v w : ℂ × ℂ) :
    Continuous (classicalHillVariationWronskian q h μ v w) :=
  ((continuous_classicalHillFlow q μ v).fst.mul (contDiff_classicalHillPotentialVariation q h μ w).continuous.snd).sub
    ((continuous_classicalHillFlow q μ v).snd.mul (contDiff_classicalHillPotentialVariation q h μ w).continuous.fst)

theorem hasDerivAt_classicalHillVariationWronskian (q h : Curve ℂ) (μ : ℂ) (v w : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillVariationWronskian q h μ v w)
      (h t*(classicalHillFlow q μ v t).1*(classicalHillFlow q μ w t).1) t := by
  have hv := hasDerivAt_classicalHillFlow q μ v t
  have hw := hasDerivAt_classicalHillPotentialVariation q h μ w t
  have hf : HasDerivAt (fun x => (classicalHillFlow q μ v x).1) (classicalHillFlow q μ v t).2 t := by
    simpa using! HasFDerivAt.hasDerivAt hv.fst
  have hg : HasDerivAt (fun x => (classicalHillFlow q μ v x).2)
      ((q t-μ)*(classicalHillFlow q μ v t).1) t := by simpa using! HasFDerivAt.hasDerivAt hv.snd
  have hh : HasDerivAt (fun x => (classicalHillPotentialVariation q h μ w x).1)
      (classicalHillPotentialVariation q h μ w t).2 t := by simpa using! HasFDerivAt.hasDerivAt hw.fst
  have hk : HasDerivAt (fun x => (classicalHillPotentialVariation q h μ w x).2)
      ((q t-μ)*(classicalHillPotentialVariation q h μ w t).1+h t*(classicalHillFlow q μ w t).1) t := by
    simpa using! HasFDerivAt.hasDerivAt hw.snd
  convert (hf.mul hk).sub (hg.mul hh) using 1 <;> first | rfl | ring

theorem classicalHillVariationWronskian_integral (q h : Curve ℂ) (μ : ℂ) (v w : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..t.val, extend h s*(classicalHillFlow q μ v s).1*(classicalHillFlow q μ w s).1)=
      classicalHillVariationWronskian q h μ v w t := by
  have hc : Continuous (fun s : ℝ => extend h s*(classicalHillFlow q μ v s).1*(classicalHillFlow q μ w s).1) :=
    ((continuous_extend h).mul (continuous_classicalHillFlow q μ v).fst).mul (continuous_classicalHillFlow q μ w).fst
  have hderiv (s : ℝ) (hs : s ∈ Ioo 0 t.val) :
      HasDerivAt (classicalHillVariationWronskian q h μ v w)
        (extend h s*(classicalHillFlow q μ v s).1*(classicalHillFlow q μ w s).1) s := by
    let x : Icc (0:ℝ) 1 := ⟨s,hs.1.le,hs.2.le.trans t.property.2⟩
    have hd := hasDerivAt_classicalHillVariationWronskian q h μ v w x
    simpa only [← extend_coe h x] using hd
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (continuous_classicalHillVariationWronskian q h μ v w).continuousOn hderiv (hc.intervalIntegrable 0 t)
  simpa only [classicalHillVariationWronskian,classicalHillPotentialVariation_zero,
    Prod.fst_zero,Prod.snd_zero,mul_zero,sub_self,sub_zero] using he

end NLS.KdV
