import NLS.KdV.HillEnergyFullProduct
import NLS.KdV.HillProductDataVariation

/-! The actual full-l2 data variation of the full literal Hill energy
product is entire in energy, and is the derivative of every data line. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

def hillEnergyFullProductDataVariation (d h : lp (fun _ : ℕ+ => ℂ) 2) (E : ℂ) : ℂ :=
  fderiv ℂ hillEnergySequenceFullProduct (E,d) (0,h)

theorem hillEnergyFullProductDataVariation_eq_section (d h : lp (fun _ : ℕ+ => ℂ) 2) (E : ℂ) :
    hillEnergyFullProductDataVariation d h E = fderiv ℂ (fun b => hillEnergySequenceFullProduct (E,b)) d h := by
  rw [NLS.ComplexAnalysis.fderiv_source_section_eq_joint hillEnergySequenceFullProduct E d
    (analyticAt_hillEnergySequenceFullProduct (E,d)).differentiableAt]
  rfl

theorem analyticOnNhd_hillEnergyFullProductDataVariation (d h : lp (fun _ : ℕ+ => ℂ) 2) :
    AnalyticOnNhd ℂ (hillEnergyFullProductDataVariation d h) univ := by
  let ev : ((ℂ × lp (fun _ : ℕ+ => ℂ) 2) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,h)
  have hp : AnalyticOnNhd ℂ hillEnergySequenceFullProduct univ := fun t _ => analyticAt_hillEnergySequenceFullProduct t
  have hd := ev.comp_analyticOnNhd hp.fderiv
  intro E _
  exact (hd (E,d) (mem_univ _)).comp (f := fun w : ℂ => (w,d)) (analyticAt_id.prod analyticAt_const)

theorem hasDerivAt_hillEnergyFullProductDataLine (E : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2) :
    HasDerivAt (fun w : ℂ => hillEnergySequenceFullProduct (E,d+w • h))
      (hillEnergyFullProductDataVariation d h E) 0 := by
  have hp := (analyticAt_hillEnergySequenceFullProduct (E,d)).differentiableAt.hasFDerivAt
  simpa only [zero_smul,add_zero] using!
    hp.comp_hasDerivAt_of_eq 0 (hasDerivAt_hillEnergyDataLine E d h) (by simp)

end NLS.KdV
