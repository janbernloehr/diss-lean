import NLS.KdV.HillOriginalPositiveEndpointContinuity
import NLS.KdV.HillRealGapSampleAsymptotics
import NLS.SequenceSpaces.PositiveSquaredLatticeMap
import NLS.ZakharovShabat.SourcePeriodicEndpointContinuity

/-! The entire original positive endpoint sequences are continuous in
the literal inverse-index l2 norm at every real native H-minus-one source. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusPositiveEndpointDisplacement (right : Bool)
    (q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a}) : lp (fun _ : ℕ+ => ℂ) 2 :=
  ⟨fun m => ((hillHminusLabels q.val q.property (if right then 2*(m:ℕ) else 2*(m:ℕ)-1):ℂ)-
    ((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ),
    hillHminusOriginal_real_gap_samples_inverseIndex_error q.val q.property _ (fun m => by
      have h := monotone_hillHminusLabels q.val q.property (show 2*(m:ℕ)-1 ≤ 2*(m:ℕ) by omega)
      cases right <;> simp only [Bool.false_eq_true,if_false,if_true] <;> exact ⟨by linarith,by linarith⟩)⟩

theorem continuousAt_hillHminusPositiveEndpointDisplacement (right : Bool)
    (q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a}) :
    ContinuousAt (hillHminusPositiveEndpointDisplacement right) q := by
  obtain ⟨B,hB⟩ := exists_hillHminusDirichletBall q.val q.property
  let T : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (B.miuraBall.actionBall.lift a)
  have hlift : ContinuousAt B.miuraBall.actionBall.lift q.val :=
    (B.miuraBall.actionBall.lift_analytic q.val hB).continuousAt
  have hT : ContinuousAt (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} => T a.val) q :=
    (hillMiuraDiagonal.continuous.continuousAt.comp hlift).comp continuous_subtype_val.continuousAt
  let u : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift q.val,
    B.miuraBall.actionBall.lift_real q.val hB q.property⟩
  let D : CoeffPair 2 → Coeff 2 := fun ψ => if right then
    canonicalPeriodicRightDisplacement (by norm_num) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ)
    else canonicalPeriodicLeftDisplacement (by norm_num) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hD : ContinuousAt D (T q.val) := by
    have h := continuousAt_sourcePeriodicEndpointDisplacements_of_realType (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property
    cases right
    · exact h.fst
    · exact h.snd
  have hfull : ContinuousAt (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
      positiveSquaredLatticeError (Real.pi:ℂ) (B.miuraBall.actionBall.shift:ℂ) (D (T a.val))) q :=
    (analyticAt_positiveSquaredLatticeError _ _ _).continuousAt.comp
      (hD.comp (f := fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} => T a.val) hT)
  apply hfull.congr_of_eventuallyEq
  have hnear : ∀ᶠ a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} in 𝓝 q, a.val ∈ B.source :=
    continuous_subtype_val.continuousAt.eventually (B.source_open.mem_nhds hB)
  filter_upwards [hnear] with a ha
  ext m
  rw [positiveSquaredLatticeError_apply]
  let v : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift a.val,
    B.miuraBall.actionBall.lift_real a.val ha a.property⟩
  have he := hillHminusLabels_pair_eq_squared_miuraDirac a.val a.property v B.miuraBall.actionBall.shift
    (B.miuraBall.actionBall.image a.val ha) (B.miuraBall.actionBall.outside a.val ha) (m:ℕ) m.pos
  have hre := hillMiuraDiracPair_real v (m:ℕ)
  symm
  cases right
  · change (((Real.pi:ℂ)*(m:ℕ)+canonicalPeriodicLeftDisplacement (by norm_num) (by norm_num)
      (periodOnePotential (T a.val)) (periodOnePotential_mem (T a.val)) (m:ℕ))^2-
      (B.miuraBall.actionBall.shift:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ) = _
    rw [canonicalPeriodicLeftDisplacement_apply]
    have hr : ((hillMiuraDiracLeft v.val (m:ℕ)).re:ℂ) = hillMiuraDiracLeft v.val (m:ℕ) := Complex.ext rfl hre.1.symm
    change _ = ((hillHminusLabels a.val a.property (2*(m:ℕ)-1):ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)
    rw [he.1,Complex.ofReal_sub,Complex.ofReal_pow,hr]
    congr 1
    dsimp only [hillMiuraDiracLeft,T,v]
    push_cast
    ring
  · change (((Real.pi:ℂ)*(m:ℕ)+canonicalPeriodicRightDisplacement (by norm_num) (by norm_num)
      (periodOnePotential (T a.val)) (periodOnePotential_mem (T a.val)) (m:ℕ))^2-
      (B.miuraBall.actionBall.shift:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ) = _
    rw [canonicalPeriodicRightDisplacement_apply]
    have hr : ((hillMiuraDiracRight v.val (m:ℕ)).re:ℂ) = hillMiuraDiracRight v.val (m:ℕ) := Complex.ext rfl hre.2.symm
    change _ = ((hillHminusLabels a.val a.property (2*(m:ℕ)):ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)
    rw [he.2,Complex.ofReal_sub,Complex.ofReal_pow,hr]
    congr 1
    dsimp only [hillMiuraDiracRight,T,v]
    push_cast
    ring

theorem continuous_hillHminusPositiveEndpointDisplacement (right : Bool) :
    Continuous (hillHminusPositiveEndpointDisplacement right) :=
  continuous_iff_continuousAt.mpr (continuousAt_hillHminusPositiveEndpointDisplacement right)

end NLS.KdV
