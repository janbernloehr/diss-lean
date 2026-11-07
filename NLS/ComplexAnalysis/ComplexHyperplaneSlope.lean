import NLS.ComplexAnalysis.ParametricCosineMeanSegment
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Holomorphic filled division along the transverse segment to a complex
linear hyperplane. Analyticity at a zero-coordinate center follows from
joint analyticity near the single constant segment there. -/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.ComplexAnalysis
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def complexHyperplanePath (l : E →L[ℂ] ℂ) (e : E) (p : ℂ × E) : E :=
  p.2-l p.2 • e+p.1 • (l p.2 • e)

def complexHyperplaneSlope (g : E → ℂ) (l : E →L[ℂ] ℂ) (e z : E) : ℂ :=
  ∫ t in (0:ℝ)..1, (fderiv ℂ g (complexHyperplanePath l e ((t:ℂ),z))) e

theorem analyticAt_complexHyperplaneSlope (g : E → ℂ) (l : E →L[ℂ] ℂ) (e x : E)
    (hg : AnalyticAt ℂ g x) (hlx : l x=0) :
    AnalyticAt ℂ (complexHyperplaneSlope g l e) x := by
  let T := complexHyperplanePath l e
  have hT (p : ℂ × E) : AnalyticAt ℂ T p :=
    (analyticAt_snd.sub (((l.analyticAt _).comp analyticAt_snd).smul analyticAt_const)).add
      (analyticAt_fst.smul (((l.analyticAt _).comp analyticAt_snd).smul analyticAt_const))
  let D : Set (ℂ × E) := {p | AnalyticAt ℂ g (T p)}
  have hD : IsOpen D := (isOpen_analyticAt ℂ g).preimage
    (continuous_iff_continuousAt.mpr (fun p => (hT p).continuousAt))
  have hF : AnalyticOnNhd ℂ (fun p : ℂ × E => (fderiv ℂ g (T p)) e) D := by
    intro p hp
    exact ((ContinuousLinearMap.apply ℂ ℂ e).analyticAt _).comp ((hp.fderiv).comp (hT p))
  apply analyticAt_intervalIntegral_of_jointAnalytic _ hD hF 0 1 x
  intro t _
  change AnalyticAt ℂ g (x-l x • e+(t:ℂ) • (l x • e))
  simpa only [hlx,zero_smul,sub_zero,smul_zero,add_zero] using hg

theorem mul_complexHyperplaneSlope (g : E → ℂ) (l : E →L[ℂ] ℂ) (e z : E)
    (hg : ∀ t ∈ uIcc (0:ℝ) 1, AnalyticAt ℂ g (complexHyperplanePath l e ((t:ℂ),z))) :
    l z*complexHyperplaneSlope g l e z=g z-g (z-l z • e) := by
  let b := z-l z • e
  have hd (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) :
      HasDerivAt (fun r : ℝ => g (b+r • (l z • e)))
        (l z*((fderiv ℂ g (b+t • (l z • e))) e)) t := by
    have hline : HasDerivAt (fun r : ℝ => b+r • (l z • e)) (l z • e) t := by
      simpa only [one_smul,id_eq] using! ((hasDerivAt_id t).smul_const (l z • e)).const_add b
    have hga : AnalyticAt ℂ g (b+t • (l z • e)) := by
      simpa only [complexHyperplanePath,Complex.coe_smul,b] using hg t ht
    have hd := (hga.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hline
    change HasDerivAt (fun r : ℝ => g (b+r • (l z • e)))
      ((fderiv ℂ g (b+t • (l z • e))) (l z • e)) t at hd
    rw [map_smul,smul_eq_mul] at hd
    exact hd

  have hc : ContinuousOn (fun t : ℝ => (fderiv ℂ g (b+t • (l z • e))) e) (uIcc (0:ℝ) 1) := by
    intro t ht
    have hga : AnalyticAt ℂ g (b+t • (l z • e)) := by
      simpa only [complexHyperplanePath,Complex.coe_smul,b] using hg t ht
    have hp : ContinuousAt (fun r : ℝ => b+r • (l z • e)) t := by fun_prop
    have hdc : ContinuousAt (fun r : ℝ => (fderiv ℂ g (b+r • (l z • e))) e) t :=
      ContinuousAt.comp (f := fun r : ℝ => b+r • (l z • e))
        (hga.fderiv.continuousAt.clm_apply continuousAt_const) hp
    exact hdc.continuousWithinAt
  have hi : IntervalIntegrable (fun t : ℝ => l z*((fderiv ℂ g (b+t • (l z • e))) e)) volume 0 1 :=
    (continuousOn_const.mul hc).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_const_mul] at h
  have h1 : b+(1:ℝ) • (l z • e)=z := by simp [b]
  simpa only [complexHyperplaneSlope,complexHyperplanePath,Complex.coe_smul,b,h1,zero_smul,add_zero] using h

end NLS.ComplexAnalysis
