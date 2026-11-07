import NLS.KdV.HillMiuraFullFractionalLift
import NLS.KdV.HillRotatedDiracSource

/-! The identical phase-rotated physical source admits an analytic
H^(1-r) realization for every 0 <= r < 1 on its original Miura patch. -/
noncomputable section
open Set Complex NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.KdV

def HillHminusMiuraActionBall.fractionalChart (B : HillHminusMiuraActionBall) : HillHminusMiuraChart where
  domain := B.source
  domain_open := B.source_open
  energyShift := (B.shift:ℂ)
  lift := B.lift
  lift_analytic := B.lift_analytic
  image := B.image

namespace HillProductEquationPatch

def rotatedDiracFractionalLift (P : HillProductEquationPatch) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) :
    WeightedCoeff (Weight.sobolev (1-r)) 2 × WeightedCoeff (Weight.sobolev (1-r)) 2 :=
  let u := P.parent.parent.miuraBall.actionBall.fractionalChart.fullFractionalLift r hr hr1 q
  (I • u,-I • u)

theorem analytic_rotatedDiracFractionalLift (P : HillProductEquationPatch)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ P.source) :
    AnalyticAt ℂ (P.rotatedDiracFractionalLift r hr hr1) q := by
  have hB : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈
      P.parent.parent.miuraBall.actionBall.source := (P.parent.subset (P.subset hq)).1
  have hu := (P.parent.parent.miuraBall.actionBall.fractionalChart.fullFractionalLift_analytic_and_coefficients
    r hr hr1 q hB).1
  exact (hu.const_smul (c := I)).prod (hu.const_smul (c := -I))

theorem rotatedDiracFractionalLift_coefficients (P : HillProductEquationPatch)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ P.source) (k : ℤ) :
    (P.rotatedDiracFractionalLift r hr hr1 q).1.val k =
        (P.rotatedDiracSource (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)).fst k ∧
      (P.rotatedDiracFractionalLift r hr hr1 q).2.val k =
        (P.rotatedDiracSource (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)).snd k := by
  have hB : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈
      P.parent.parent.miuraBall.actionBall.source := (P.parent.subset (P.subset hq)).1
  have hu := (P.parent.parent.miuraBall.actionBall.fractionalChart.fullFractionalLift_analytic_and_coefficients
    r hr hr1 q hB).2 k
  constructor
  · change I*(P.parent.parent.miuraBall.actionBall.fractionalChart.fullFractionalLift r hr hr1 q).val k =
      (sourcePhase (hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift
        (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)))).fst k
    rw [sourcePhase_fst,hillMiuraDiagonal_fst,hu]
    rfl
  · change -I*(P.parent.parent.miuraBall.actionBall.fractionalChart.fullFractionalLift r hr hr1 q).val k =
      (sourcePhase (hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift
        (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)))).snd k
    rw [sourcePhase_snd,hillMiuraDiagonal_snd,hu]
    rfl

end HillProductEquationPatch
end NLS.KdV
