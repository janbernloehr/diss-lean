import NLS.ZakharovShabat.ClassicalFundamentalSolution
import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity

/-! # Wronskian conservation for locally absolutely continuous physical solutions -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The determinant of two physical pair vectors. -/
def physicalWronskian (v w : ℂ × ℂ) : ℂ := v.1*w.2-v.2*w.1

theorem absolutelyContinuousOnInterval_physicalWronskian (F G : ℝ → ℂ × ℂ)
    (a b : ℝ) (hF : AbsolutelyContinuousOnInterval F a b)
    (hG : AbsolutelyContinuousOnInterval G a b) :
    AbsolutelyContinuousOnInterval (fun t => physicalWronskian (F t) (G t)) a b := by
  have hf1 := absolutelyContinuousOnInterval_clm hF (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hf2 := absolutelyContinuousOnInterval_clm hF (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hg1 := absolutelyContinuousOnInterval_clm hG (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hg2 := absolutelyContinuousOnInterval_clm hG (ContinuousLinearMap.snd ℝ ℂ ℂ)
  simpa [physicalWronskian,Pi.sub_def,Pi.smul_def,smul_eq_mul] using! (hf1.smul hg2).sub (hf2.smul hg1)

/-- The trace-zero original coefficient makes the Wronskian derivative vanish. -/
theorem hasDerivAt_physicalWronskian (φ F G : ℝ → ℂ × ℂ) (z : ℂ) (t : ℝ)
    (hF : HasDerivAt F (classicalODECoefficient (φ t) z (F t)) t)
    (hG : HasDerivAt G (classicalODECoefficient (φ t) z (G t)) t) :
    HasDerivAt (fun s => physicalWronskian (F s) (G s)) 0 t := by
  convert! (((HasFDerivAt.hasDerivAt hF.fst).mul (HasFDerivAt.hasDerivAt hG.snd)).sub
    ((HasFDerivAt.hasDerivAt hF.snd).mul (HasFDerivAt.hasDerivAt hG.fst))) using 1
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
    one_smul,classicalODECoefficient_apply]
  simp
  ring

/-- Wronskian conservation requires the locally AC solution hypothesis,
not merely satisfaction of the differential equation almost everywhere. -/
theorem physicalWronskian_const_of_AC_solutions (φ F G : ℝ → ℂ × ℂ) (z : ℂ)
    (hF : ∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b)
    (hG : ∀ a b : ℝ, AbsolutelyContinuousOnInterval G a b)
    (hdF : ∀ᵐ t : ℝ, HasDerivAt F (classicalODECoefficient (φ t) z (F t)) t)
    (hdG : ∀ᵐ t : ℝ, HasDerivAt G (classicalODECoefficient (φ t) z (G t)) t)
    (a b : ℝ) : physicalWronskian (F b) (G b) = physicalWronskian (F a) (G a) := by
  have hd : ∀ᵐ t : ℝ, t ∈ Set.uIcc a b →
      HasDerivAt (fun s => physicalWronskian (F s) (G s)) 0 t := by
    filter_upwards [hdF,hdG] with t htF htG _
    exact hasDerivAt_physicalWronskian φ F G z t htF htG
  obtain ⟨c,hc⟩ := (absolutelyContinuousOnInterval_physicalWronskian F G a b
    (hF a b) (hG a b)).const_of_ae_hasDerivAt_zero hd
  exact (hc b (by simp)).trans (hc a (by simp)).symm

end NLS.ZakharovShabat
