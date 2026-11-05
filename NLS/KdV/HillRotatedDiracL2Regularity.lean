import NLS.KdV.HillMiuraL2AnalyticRegularity
import NLS.KdV.HillRotatedDiracSource

/-! The SAME phase-rotated source used by the actual Hill spectral core
has a complex analytic H1 representative on L2 data. The comparison
retains both components and every original coefficient. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

theorem l2Source_open (P : HillProductEquationPatch) : IsOpen {q : Coeff 2 | periodOneL2Inclusion q ∈ P.source} :=
  P.source_open.preimage periodOneL2Inclusion.continuous

def rotatedDiracL2Lift (P : HillProductEquationPatch) (q : Coeff 2) :
    ScalarDomain 2 × ScalarDomain 2 :=
  let u := P.parent.parent.miuraBall.actionBall.l2Lift q
  (I • u, -I • u)

theorem analytic_rotatedDiracL2Lift (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source) : AnalyticAt ℂ P.rotatedDiracL2Lift q := by
  have hB : periodOneL2Inclusion q ∈ P.parent.parent.miuraBall.actionBall.source :=
    (P.parent.subset (P.subset hq)).1
  have hu := P.parent.parent.miuraBall.actionBall.analytic_l2Lift q hB
  exact (hu.const_smul (c := I)).prod (hu.const_smul (c := -I))

theorem sobolevSourceInclusion_rotatedDiracL2Lift (P : HillProductEquationPatch)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.source) :
    sobolevSourceInclusion (P.rotatedDiracL2Lift q) =
      P.rotatedDiracSource (periodOneL2Inclusion q) := by
  have hB : periodOneL2Inclusion q ∈ P.parent.parent.miuraBall.actionBall.source :=
    (P.parent.subset (P.subset hq)).1
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext k
    change (sobolevSourceInclusion (P.rotatedDiracL2Lift q)).fst k =
      (sourcePhase (hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift
        (periodOneL2Inclusion q)))).fst k
    simp only [sobolevSourceInclusion_fst, sourcePhase_fst, hillMiuraDiagonal_fst,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    change I * (P.parent.parent.miuraBall.actionBall.l2Lift q).val k = _
    rw [HillHminusMiuraActionBall.l2Lift_apply _ q hB]
  · ext k
    change (sobolevSourceInclusion (P.rotatedDiracL2Lift q)).snd k =
      (sourcePhase (hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift
        (periodOneL2Inclusion q)))).snd k
    simp only [sobolevSourceInclusion_snd, sourcePhase_snd, hillMiuraDiagonal_snd,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    change -I * (P.parent.parent.miuraBall.actionBall.l2Lift q).val k = _
    rw [HillHminusMiuraActionBall.l2Lift_apply _ q hB]

end NLS.KdV.HillProductEquationPatch
