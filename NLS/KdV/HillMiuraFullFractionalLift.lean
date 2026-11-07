import NLS.KdV.HillMiuraThirdOrderLift
import NLS.SequenceSpaces.FractionalMiuraRecovery

/-! # Analytic physical Miura lifts throughout the negative Hilbert scale

For every 0 <= r < 1, the actual L2 lift has an analytic H^(1-r)
realization. The lower-r range uses the fixed third-order realization
and an explicit massive-resolvent recovery of the same coefficients.
-/
noncomputable section
open Complex NLS.WeightedCoeff
namespace NLS.KdV.HillHminusMiuraChart

def fullFractionalLift (C : HillHminusMiuraChart) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) : WeightedCoeff (Weight.sobolev (1-r)) 2 :=
  if h : 1/2 < r then C.fractionalLift r hr1.le q else
    fractionalMiuraRecovery r hr C.energyShift q (C.thirdOrderLift r (by linarith) q)

theorem thirdOrderLift_miura_equation (C : HillHminusMiuraChart)
    (r : ℝ) (hr : r ≤ 2/3) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ C.domain) (k : ℤ) :
    2*I*(Real.pi:ℂ)*k*(C.thirdOrderLift r hr q).val k+
      ∑' j : ℤ, (C.thirdOrderLift r hr q).val (k-j)*(C.thirdOrderLift r hr q).val j =
      q.val k+(Pi.single (0:ℤ) C.energyShift : ℤ → ℂ) k := by
  have hc := (C.thirdOrderLift_analytic_and_coefficients r hr q hq).2
  simp only [hc]
  have he := congrArg (fun a : PeriodOneHminusOne => a.val k)
    (C.image (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q) hq)
  simpa only [periodOneMiura_apply,WeightedCoeff.add_val,periodOneL2Inclusion_apply,
    sobolevInclusion_apply,lp.single_apply] using he

theorem fullFractionalLift_analytic_and_coefficients (C : HillHminusMiuraChart)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ C.domain) :
    AnalyticAt ℂ (C.fullFractionalLift r hr hr1) q ∧
      ∀ k, (C.fullFractionalLift r hr hr1 q).val k =
        C.lift (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q) k := by
  by_cases h : 1/2 < r
  · have hf : C.fullFractionalLift r hr hr1 = C.fractionalLift r hr1.le := by
      funext a
      simp only [fullFractionalLift,dif_pos h]
    rw [hf]
    exact C.fractionalLift_analytic_and_coefficients r h hr1 q hq
  · have hr2 : r ≤ 2/3 := by linarith
    obtain ⟨ha,hc⟩ := C.thirdOrderLift_analytic_and_coefficients r hr2 q hq
    have hcomp := (analyticAt_fractionalMiuraRecovery r hr C.energyShift
      (q,C.thirdOrderLift r hr2 q)).comp
        (f := fun a => (a,C.thirdOrderLift r hr2 a)) (analyticAt_id.prod ha)
    have hpoint (k : ℤ) :
        (fractionalMiuraRecovery r hr C.energyShift q (C.thirdOrderLift r hr2 q)).val k =
          C.lift (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q) k :=
      (fractionalMiuraRecovery_eq_of_equation r hr C.energyShift q (C.thirdOrderLift r hr2 q)
        (C.thirdOrderLift_miura_equation r hr2 q hq) k).trans (hc k)
    have hf : C.fullFractionalLift r hr hr1 = fun a =>
        fractionalMiuraRecovery r hr C.energyShift a (C.thirdOrderLift r hr2 a) := by
      funext a
      simp only [fullFractionalLift,dif_neg h]
    rw [hf]
    exact ⟨hcomp,hpoint⟩

end NLS.KdV.HillHminusMiuraChart
