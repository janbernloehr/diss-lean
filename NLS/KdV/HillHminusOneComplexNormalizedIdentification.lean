import NLS.KdV.HillHminusOneMiuraNormalizedIdentification
import NLS.SequenceSpaces.PeriodOneRealFormIdentity

/-! # Actual normalized-family identification for complex sources near zero

The proved physical real-form identity extends the actual real-input
identification to every complex source in the same connected norm ball.
No global or arbitrary-base neighborhood claim is made.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat

namespace NLS.KdV

/-- The actual real-input identification extends to all complex inputs on the same ball, retaining the constructed normalized data. -/
theorem exists_hillHminus_complex_normalized_family_identification (Dold : HillHminusMiuraChart)
    {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
    (D : HillHminusUniformPeriodData Dold N V A)
    (T R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (hentry : ∀ q ∈ V, ∀ m j : ℤ, (T q (lp.single 2 j 1)) m = hillHminusPeriodMatrix Dold N q m j)
    (hRT : ∀ q ∈ V, (R q).comp (T q) = ContinuousLinearMap.id ℂ (Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) :
    ∃ C : HillHminusMiuraChart, ∃ δ : ℝ, ∃ W₀ W : Set (CoeffPair 2),
      ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ V ∧
        ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n)
          (univ ×ˢ ball (0 : PeriodOneHminusOne) δ)) ∧
        ∀ q ∈ ball (0 : PeriodOneHminusOne) δ,
          ∀ n : ℕ+, ∀ energy : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,q) =
            hillHminusNormalizedNumerator Dold N R n (energy,q) := by
  obtain ⟨C,δ,W₀,W,s,hδ,hδV,hδC,H,hW,hpsi,hreal⟩ :=
    exists_hillHminus_real_normalized_family_identification Dold D T R hentry hRT
  refine ⟨C,δ,W₀,W,s,hδ,hδV,hδC,H,hW,hpsi,?_⟩
  intro q hq n energy
  let F := fun p => hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,p)
  let G := fun p => hillHminusNormalizedNumerator Dold N R n (energy,p)
  have hF : AnalyticOnNhd ℂ F (Metric.ball (0 : PeriodOneHminusOne) δ) := by
    intro p hp
    exact ((hpsi (n : ℤ)) (energy,p) ⟨Set.mem_univ _,hp⟩).comp
      (f := fun p : PeriodOneHminusOne => (energy,p)) (analyticAt_const.prod analyticAt_id)
  have hG : AnalyticOnNhd ℂ G (Metric.ball (0 : PeriodOneHminusOne) δ) := by
    intro p hp
    exact ((D.normalizedNumerator_analytic R hRa n) (energy,p) ⟨Set.mem_univ _,hδV hp⟩).comp
      (f := fun p : PeriodOneHminusOne => (energy,p)) (analyticAt_const.prod analyticAt_id)
  have he := NLS.periodOneHminus_real_form_identity Metric.isOpen_ball Metric.isPreconnected_ball
    (Metric.mem_ball_self hδ) F G hF hG (fun p hp hpr => hreal p hp hpr n energy)
  exact he hq

end NLS.KdV

namespace NLS.KdV

/-- Actual analytic weighted inverses and normalized NLS data identify the
Miura family on the whole complex ball, with the exact inverse bounds and
weighted compatibility retained. -/
theorem exists_hillHminus_actual_complex_twoWeighted_normalized_identification :
    ∃ Dold : HillHminusMiuraChart, ∃ N : ℕ, ∃ C : HillHminusMiuraChart, ∃ δ : ℝ,
      ∃ W₀ W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
      ∃ R Q : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2), ∃ A : ℝ,
        0 < δ ∧ HillHminusUniformPeriodData Dold N (ball (0 : PeriodOneHminusOne) δ) A ∧
        ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n)
          (univ ×ˢ ball (0 : PeriodOneHminusOne) δ)) ∧
        AnalyticOnNhd ℂ R (ball (0 : PeriodOneHminusOne) δ) ∧
        AnalyticOnNhd ℂ Q (ball (0 : PeriodOneHminusOne) δ) ∧
        R 0 = ContinuousLinearMap.id ℂ (Coeff 2) ∧ Q 0 = ContinuousLinearMap.id ℂ (Coeff 2) ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ‖R q‖ ≤ 2 ∧ ‖Q q‖ ≤ 2 ∧
          ∀ m n : ℤ, Coeff.positiveIndexWeight m^2*(R q (lp.single 2 n 1)) m =
            Coeff.positiveIndexWeight n^2*(Q q (lp.single 2 n 1)) m) ∧
        ∀ q ∈ ball (0 : PeriodOneHminusOne) δ,
          ∀ n : ℕ+, ∀ energy : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,q) =
            hillHminusNormalizedNumerator Dold N R n (energy,q) := by
  obtain ⟨Dold,N,C,δ,W₀,W,s,R,Q,A,hδ,D,hδC,H,hW,hpsi,hRa,hQa,hR0,hQ0,hbounds,hreal⟩ :=
    exists_hillHminus_actual_twoWeighted_normalized_identification
  refine ⟨Dold,N,C,δ,W₀,W,s,R,Q,A,hδ,D,hδC,H,hW,hpsi,hRa,hQa,hR0,hQ0,hbounds,?_⟩
  intro q hq n energy
  let F := fun p => hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,p)
  let G := fun p => hillHminusNormalizedNumerator Dold N R n (energy,p)
  have hF : AnalyticOnNhd ℂ F (ball (0 : PeriodOneHminusOne) δ) := by
    intro p hp
    exact ((hpsi (n : ℤ)) (energy,p) ⟨mem_univ _,hp⟩).comp
      (f := fun p : PeriodOneHminusOne => (energy,p)) (analyticAt_const.prod analyticAt_id)
  have hG : AnalyticOnNhd ℂ G (ball (0 : PeriodOneHminusOne) δ) := by
    intro p hp
    exact ((D.normalizedNumerator_analytic R hRa n) (energy,p) ⟨mem_univ _,hp⟩).comp
      (f := fun p : PeriodOneHminusOne => (energy,p)) (analyticAt_const.prod analyticAt_id)
  exact (periodOneHminus_real_form_identity isOpen_ball isPreconnected_ball (mem_ball_self hδ)
    F G hF hG (fun p hp hpr => hreal p hp hpr n energy)) hq

end NLS.KdV
