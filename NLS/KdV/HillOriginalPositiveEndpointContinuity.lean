import NLS.KdV.HminusOneDirichletAnalyticBalls
import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.ZakharovShabat.PeriodOneBoundaryInterlacing

/-! The FULL ORIGINAL indexed positive Hill endpoints are continuous
on the ENTIRE native H-minus-one real form. A fixed local real-preserving
Miura lift and its outside-spectrum constant identify every original
pair with the corresponding squared continuous Dirac endpoints.
Low indices and collapsed or repeated endpoints are retained. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem continuousAt_hillHminusPositiveGapEndpoints
    (m : ℕ+) (q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a}) :
    ContinuousAt (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
      hillHminusLabels a.val a.property (2*(m:ℕ)-1)) q ∧
    ContinuousAt (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
      hillHminusLabels a.val a.property (2*(m:ℕ))) q := by
  obtain ⟨B,hB⟩ := exists_hillHminusDirichletBall q.val q.property
  let T : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (B.miuraBall.actionBall.lift a)
  have hlift : ContinuousAt B.miuraBall.actionBall.lift q.val :=
    (B.miuraBall.actionBall.lift_analytic q.val hB).continuousAt
  have hT : ContinuousAt (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} => T a.val) q :=
    (hillMiuraDiagonal.continuous.continuousAt.comp hlift).comp continuous_subtype_val.continuousAt
  let u : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift q.val,
    B.miuraBall.actionBall.lift_real q.val hB q.property⟩
  have hL := (continuousAt_canonicalPeriodicLeft_periodOne_of_realType (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ)).comp
      (f := fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} => T a.val) hT
  have hR := (continuousAt_canonicalPeriodicRight_periodOne_of_realType (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ)).comp
      (f := fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} => T a.val) hT
  have hleft : ContinuousAt (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
      (hillMiuraDiracLeft (B.miuraBall.actionBall.lift a.val) ((m:ℕ):ℤ)).re^2-
        B.miuraBall.actionBall.shift) q :=
    ((continuous_re.continuousAt.comp hL).pow 2).sub continuousAt_const
  have hright : ContinuousAt (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
      (hillMiuraDiracRight (B.miuraBall.actionBall.lift a.val) ((m:ℕ):ℤ)).re^2-
        B.miuraBall.actionBall.shift) q :=
    ((continuous_re.continuousAt.comp hR).pow 2).sub continuousAt_const
  have hnear : ∀ᶠ a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} in 𝓝 q, a.val ∈ B.source :=
    continuous_subtype_val.continuousAt.eventually (B.source_open.mem_nhds hB)
  constructor
  · apply hleft.congr_of_eventuallyEq
    filter_upwards [hnear] with a ha
    let v : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift a.val,
      B.miuraBall.actionBall.lift_real a.val ha a.property⟩
    exact (hillHminusLabels_pair_eq_squared_miuraDirac a.val a.property v B.miuraBall.actionBall.shift
      (B.miuraBall.actionBall.image a.val ha) (B.miuraBall.actionBall.outside a.val ha) (m:ℕ) m.pos).1
  · apply hright.congr_of_eventuallyEq
    filter_upwards [hnear] with a ha
    let v : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift a.val,
      B.miuraBall.actionBall.lift_real a.val ha a.property⟩
    exact (hillHminusLabels_pair_eq_squared_miuraDirac a.val a.property v B.miuraBall.actionBall.shift
      (B.miuraBall.actionBall.image a.val ha) (B.miuraBall.actionBall.outside a.val ha) (m:ℕ) m.pos).2

theorem continuous_hillHminusPositiveGapEndpoints (m : ℕ+) :
    Continuous (fun q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a} =>
      hillHminusLabels q.val q.property (2*(m:ℕ)-1)) ∧
    Continuous (fun q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a} =>
      hillHminusLabels q.val q.property (2*(m:ℕ))) :=
  ⟨continuous_iff_continuousAt.mpr (fun q => (continuousAt_hillHminusPositiveGapEndpoints m q).1),
    continuous_iff_continuousAt.mpr (fun q => (continuousAt_hillHminusPositiveGapEndpoints m q).2)⟩

end NLS.KdV
