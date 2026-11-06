import NLS.MKdV.MiuraL2ActionSequence
import NLS.MKdV.MiuraMassActionTrace
import NLS.ZakharovShabat.ScalarRealL2Density

/-! # The full original L² mass trace

Norm continuity of the actual first action moment and physical real H¹
density extend the independently identified mass trace to every real L²
profile, including zero mean and collapsed actions.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.Poisson
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraL2Mass (a : Coeff 2) : ℂ := (1/2 : ℂ)*reflectedHilbertPairing a a

theorem miuraL2Mass_eq_mean_sq_add_actionMoment (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    miuraL2Mass a = (1/2 : ℂ)*(a 0)^2+miuraL2ActionMoment a := by
  have he := realL2_eq_of_realH1_agreement
    (fun b => miuraL2Mass b-(1/2 : ℂ)*(b 0)^2) miuraL2ActionMoment ?_ a ha ?_
      (analyticAt_miuraL2ActionMoment a ha).continuousAt
  · exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  · intro b hb
    rw [miuraL2ActionMoment_original_H1 b hb]
    have h : miuraL2Mass (scalarInclusion b) = (1/2 : ℂ)*(scalarInclusion b 0)^2+miuraH1ActionMoment b := by
      simpa only [miuraL2Mass,miuraH1Mass,scalarInclusion_apply] using! miuraH1Mass_eq_mean_sq_add_actionMoment b hb
    linear_combination h
  · exact ((analyticAt_const.mul ((reflectedHilbertPairing.analyticAt_bilinear _).comp₂
      analyticAt_id analyticAt_id)).sub
        (analyticAt_const.mul (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).analyticAt a).pow 2))).continuousAt

end NLS.MKdV
