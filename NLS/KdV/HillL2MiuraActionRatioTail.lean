import NLS.KdV.HillMiuraL2AnalyticRegularity
import NLS.KdV.HillMiuraNormalizedRatioLocalData
import NLS.ZakharovShabat.SourceHigherActionOneSobolevRatio
import NLS.ZakharovShabat.SourceSobolevNormalizedCoordinates

/-! The exact LOCAL Miura normalized Hill action ratio has one-order
decay on ONE complex L2 neighborhood before all high positive indices.
The canonical global ratio is not substituted for the local formula. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV.HillHminusMiuraActionBall

def l2DiracLift (B : HillHminusMiuraActionBall) (q : Coeff 2) : ScalarDomain 2 × ScalarDomain 2 :=
  (B.l2Lift q,B.l2Lift q)

theorem analytic_l2DiracLift (B : HillHminusMiuraActionBall) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ B.source) : AnalyticAt ℂ B.l2DiracLift q :=
  (B.analytic_l2Lift q hq).prod (B.analytic_l2Lift q hq)

theorem sobolevSourceInclusion_l2DiracLift (B : HillHminusMiuraActionBall) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ B.source) :
    sobolevSourceInclusion (B.l2DiracLift q) = hillMiuraDiagonal (B.lift (periodOneL2Inclusion q)) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext k
    change (sobolevSourceInclusion (B.l2DiracLift q)).fst k =
      (hillMiuraDiagonal (B.lift (periodOneL2Inclusion q))).fst k
    simp only [sobolevSourceInclusion_fst,hillMiuraDiagonal_fst,l2DiracLift]
    change (B.l2Lift q).val k = B.lift (periodOneL2Inclusion q) k
    exact B.l2Lift_apply q hq k
  · ext k
    change (sobolevSourceInclusion (B.l2DiracLift q)).snd k =
      (hillMiuraDiagonal (B.lift (periodOneL2Inclusion q))).snd k
    simp only [sobolevSourceInclusion_snd,hillMiuraDiagonal_snd,l2DiracLift]
    change (B.l2Lift q).val k = B.lift (periodOneL2Inclusion q) k
    exact B.l2Lift_apply q hq k

end NLS.KdV.HillHminusMiuraActionBall
namespace NLS.KdV.HillHminusMiuraGapBall

private theorem normalizedRatio_eq_firstMoment (B : HillHminusMiuraGapBall) (n : ℕ+)
    (q : PeriodOneHminusOne) :
    B.normalizedRatio n q = (4*((Real.pi:ℂ)*(n:ℕ)))*
      sourceHigherActionOneNormalized (by simp) (by norm_num) (n:ℕ) (hillMiuraDiagonal (B.actionBall.lift q)) /
        (sourceStandardRootMidpoint (by simp) (by norm_num) (hillMiuraDiagonal (B.actionBall.lift q)) (n:ℕ))^2 := by
  unfold normalizedRatio diracSum
  ring

private theorem real_l2_normalized_source (B : HillHminusMiuraGapBall) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ B.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    IsRealType (CoeffPair.toMax 2 (sobolevNormalizedCoordinates (B.actionBall.l2DiracLift q))) := by
  rw [sobolevNormalizedCoordinates_realType_iff,B.actionBall.sobolevSourceInclusion_l2DiracLift q hq]
  exact (hillMiuraRealSource ⟨B.actionBall.lift (periodOneL2Inclusion q),
    B.actionBall.lift_real _ hq hr⟩).property

private theorem eventually_l2_normalized_in (B : HillHminusMiuraGapBall) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ B.source) (V : Set (CoeffPair 2)) (hV : IsOpen V)
    (hqV : sobolevNormalizedCoordinates (B.actionBall.l2DiracLift q) ∈ V) :
    ∀ᶠ r in 𝓝 q, sobolevNormalizedCoordinates (B.actionBall.l2DiracLift r) ∈ V :=
  ((sobolevNormalizedCoordinates.analyticAt _).comp
    (B.actionBall.analytic_l2DiracLift q hq)).continuousAt.tendsto.eventually (hV.mem_nhds hqV)

theorem exists_local_l2Miura_normalizedRatio_tail_bound (B : HillHminusMiuraGapBall)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ B.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ B.source) ∧ ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ r ∈ U, ∀ n : ℕ+, N ≤ (n:ℕ) →
        (1+(n:ℝ))*‖B.normalizedRatio n (periodOneL2Inclusion r)-1‖ ≤ C := by
  obtain ⟨V,hV,hqV,N,C,hC,hbound⟩ := exists_local_normalizedSobolevHigherActionOneRatio_decay
    ⟨sobolevNormalizedCoordinates (B.actionBall.l2DiracLift q),B.real_l2_normalized_source q hq hr⟩
  have hsource : ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ B.source :=
    periodOneL2Inclusion.continuous.continuousAt.tendsto.eventually (B.source_open.mem_nhds hq)
  have hall : ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ B.source ∧
      ∀ n : ℕ+, N ≤ (n:ℕ) → (1+(n:ℝ))*‖B.normalizedRatio n (periodOneL2Inclusion r)-1‖ ≤ C :=
    (hsource.and (B.eventually_l2_normalized_in q hq V hV hqV)).mono (fun r h => by
      refine ⟨h.1,?_⟩
      intro n hn
      have hb := hbound _ h.2 n hn
      dsimp only at hb
      rw [normalizedWeightedSource_sobolevNormalizedCoordinates,
        B.actionBall.sobolevSourceInclusion_l2DiracLift r h.1] at hb
      rw [B.normalizedRatio_eq_firstMoment]
      exact hb)
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp hall
  exact ⟨U,hU,hqU,fun r hrU => (hUsub hrU).1,N,C,hC,fun r hrU => (hUsub hrU).2⟩

end NLS.KdV.HillHminusMiuraGapBall
