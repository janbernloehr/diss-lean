import NLS.KdV.HillHminusOneMiuraActionBalls
import NLS.SequenceSpaces.AnalyticMiuraH1Recovery
import NLS.SequenceSpaces.AnalyticMiuraSmoothingRemainder

/-! Actual Hill action-ball Miura lifts restricted to complex L2 data.
The original lift has an analytic H1 representative on the same source
preimage. Its nonlinear remainder after the exact massive principal
term is analytic in H2, with the original constant energy shift explicit. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV.HillHminusMiuraActionBall

theorem l2Source_open (B : HillHminusMiuraActionBall) : IsOpen {q : Coeff 2 | periodOneL2Inclusion q ∈ B.source} :=
  B.source_open.preimage periodOneL2Inclusion.continuous

private theorem image_on_source (B : HillHminusMiuraActionBall) (q : PeriodOneHminusOne)
    (hq : q ∈ B.source) : periodOneMiura (B.lift q) =
      q + periodOneL2Inclusion (lp.single 2 0 (B.shift : ℂ)) := B.image q hq

private theorem lift_analytic_on_source (B : HillHminusMiuraActionBall) (q : PeriodOneHminusOne)
    (hq : q ∈ B.source) : AnalyticAt ℂ B.lift q := B.lift_analytic q hq

def l2Forcing (B : HillHminusMiuraActionBall) (q : Coeff 2) : Coeff 2 :=
  q + lp.single 2 0 (B.shift : ℂ)

theorem l2WeakEquation (B : HillHminusMiuraActionBall) (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ B.source)
    (j : ℤ) : 2 * I * (Real.pi : ℂ) * j * B.lift (periodOneL2Inclusion q) j +
      ∑' i : ℤ, B.lift (periodOneL2Inclusion q) (j-i) * B.lift (periodOneL2Inclusion q) i =
        B.l2Forcing q j := by
  have he : periodOneMiura (B.lift (periodOneL2Inclusion q)) =
      periodOneL2Inclusion (B.l2Forcing q) :=
    (B.image_on_source (periodOneL2Inclusion q) hq).trans
      (periodOneL2Inclusion.map_add q (lp.single 2 0 (B.shift : ℂ))).symm
  exact periodOneMiura_equation_of_image (B.l2Forcing q) (B.lift (periodOneL2Inclusion q)) he j

def l2Lift (B : HillHminusMiuraActionBall) (q : Coeff 2) : ZakharovShabat.ScalarDomain 2 :=
  periodOneMiuraH1Recovery (B.l2Forcing q)
    (B.lift (periodOneL2Inclusion q))

private theorem forcing_analytic (B : HillHminusMiuraActionBall) (q : Coeff 2) :
    AnalyticAt ℂ B.l2Forcing q := analyticAt_id.add analyticAt_const

private theorem raw_lift_analytic (B : HillHminusMiuraActionBall) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ B.source) :
    AnalyticAt ℂ (fun a : Coeff 2 => B.lift (periodOneL2Inclusion a)) q :=
  analyticAt_comp_periodOneL2Inclusion B.lift q (B.lift_analytic_on_source _ hq)

theorem analytic_l2Lift (B : HillHminusMiuraActionBall) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ B.source) : AnalyticAt ℂ B.l2Lift q := by
  have h := analyticAt_periodOneMiuraH1Recovery_comp B.l2Forcing
    (fun a => B.lift (periodOneL2Inclusion a)) q (B.forcing_analytic q) (B.raw_lift_analytic q hq)
  exact h.congr (Filter.Eventually.of_forall (fun _ => rfl))

theorem l2Lift_apply (B : HillHminusMiuraActionBall) (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ B.source)
    (k : ℤ) : (B.l2Lift q).val k = B.lift (periodOneL2Inclusion q) k := by
  exact periodOneMiuraH1Recovery_apply_of_equation (B.l2Forcing q)
    (B.lift (periodOneL2Inclusion q)) (B.l2WeakEquation q hq) k

theorem scalarInclusion_l2Lift (B : HillHminusMiuraActionBall) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ B.source) :
    ZakharovShabat.scalarInclusion (B.l2Lift q) = B.lift (periodOneL2Inclusion q) := by
  ext k
  rw [ZakharovShabat.scalarInclusion_apply, B.l2Lift_apply q hq]

theorem l2Lift_equation (B : HillHminusMiuraActionBall) (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ B.source)
    (k : ℤ) : 2 * I * (Real.pi : ℂ) * k * (B.l2Lift q).val k +
      ∑' j : ℤ, (B.l2Lift q).val (k-j) * (B.l2Lift q).val j =
        B.l2Forcing q k := by
  simp only [B.l2Lift_apply q hq]
  exact B.l2WeakEquation q hq k

def l2SmoothingRemainder (B : HillHminusMiuraActionBall) (q : Coeff 2) :
    WeightedCoeff (Weight.sobolev (1 + 1)) 2 :=
  periodOneMiuraSmoothingRemainder (B.l2Lift q)

theorem analytic_l2SmoothingRemainder (B : HillHminusMiuraActionBall) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ B.source) : AnalyticAt ℂ B.l2SmoothingRemainder q := by
  exact (analyticAt_periodOneMiuraSmoothingRemainder _).comp (B.analytic_l2Lift q hq)

theorem l2SmoothingRemainder_apply (B : HillHminusMiuraActionBall) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ B.source) (k : ℤ) :
    (B.l2SmoothingRemainder q).val k = B.lift (periodOneL2Inclusion q) k -
      (periodOneMassSymbol 0 k)⁻¹ * B.l2Forcing q k := by
  exact (periodOneMiuraSmoothingRemainder_apply_of_equation _ _ (B.l2Lift_equation q hq) k).trans
    (congrArg (fun z : ℂ => z - (periodOneMassSymbol 0 k)⁻¹ *
      B.l2Forcing q k) (B.l2Lift_apply q hq k))

end NLS.KdV.HillHminusMiuraActionBall
