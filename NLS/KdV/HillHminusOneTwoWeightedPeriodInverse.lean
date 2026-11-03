import NLS.KdV.HillHminusOneTwoWeightedPeriodOperator
import NLS.KdV.HillHminusOnePeriodInverse
import NLS.SequenceSpaces.DiagonalIntertwining
import NLS.ComplexAnalysis.AnalyticOperatorInverse

/-! # Compatible twice-weighted and unweighted Hill period inverses

The bounded reciprocal diagonal intertwines the two actual period maps.
Their constructed analytic inverses therefore give exactly compatible
columns. In particular the original inverse columns have two index weights
in l2, rather than merely coordinatewise decay.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

theorem hillHminus_period_twoWeight_intertwine (C : HillHminusMiuraChart) (N : ℕ) (q : PeriodOneHminusOne)
    (T S : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)
    (hT : ∀ m n : ℤ, (T (lp.single 2 n 1)) m = hillHminusPeriodMatrix C N q m n)
    (hS : ∀ m n : ℤ, (S (lp.single 2 n 1)) m = hillHminusTwoWeightedPeriodMatrix C N q m n) :
    T.comp (NLS.Coeff.multiplierCLM (NLS.Coeff.positiveIndexPowerReciprocal 2)) =
      (NLS.Coeff.multiplierCLM (NLS.Coeff.positiveIndexPowerReciprocal 2)).comp S := by
  apply NLS.Coeff.intertwine_diagonal_of_entries (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro m n
  rw [hT,hS,hillHminusTwoWeightedPeriodMatrix,NLS.Coeff.positiveIndexPowerReciprocal_apply,
    NLS.Coeff.positiveIndexPowerReciprocal_apply]
  field_simp [NLS.Coeff.positiveIndexWeight_ne_zero]

theorem hillHminus_inverse_twoWeight_entries (C : HillHminusMiuraChart) (N : ℕ) (q : PeriodOneHminusOne)
    (T S R Q : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)
    (hT : ∀ m n : ℤ, (T (lp.single 2 n 1)) m = hillHminusPeriodMatrix C N q m n)
    (hS : ∀ m n : ℤ, (S (lp.single 2 n 1)) m = hillHminusTwoWeightedPeriodMatrix C N q m n)
    (hRT : R.comp T = ContinuousLinearMap.id ℂ (NLS.Coeff 2))
    (hSQ : S.comp Q = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (m n : ℤ) :
    NLS.Coeff.positiveIndexWeight m^2*(R (lp.single 2 n 1)) m =
      NLS.Coeff.positiveIndexWeight n^2*(Q (lp.single 2 n 1)) m := by
  have he := NLS.Coeff.inverse_diagonal_entries (NLS.Coeff.positiveIndexPowerReciprocal 2) T S R Q
    (hillHminus_period_twoWeight_intertwine C N q T S hT hS) hRT hSQ m n
  simp only [NLS.Coeff.positiveIndexPowerReciprocal_apply] at he
  field_simp [NLS.Coeff.positiveIndexWeight_ne_zero] at he
  simpa only [mul_comm] using he

/-- Both actual inverses are chosen on one common neighborhood, with exact
weighted compatibility and all original spectral data retained. -/
theorem exists_hillHminus_twoWeighted_period_inverse :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne),
      ∃ T R S Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧
        AnalyticOnNhd ℂ T V ∧ AnalyticOnNhd ℂ R V ∧
        AnalyticOnNhd ℂ S V ∧ AnalyticOnNhd ℂ Q V ∧
        T 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        S 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ q ∈ V, (T q).comp (R q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
          (R q).comp (T q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
          (S q).comp (Q q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
          (Q q).comp (S q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
          ‖R q‖ ≤ 2 ∧ ‖Q q‖ ≤ 2) ∧
        (∀ q ∈ V, ∀ m n : ℤ,
          (T q (lp.single 2 n 1)) m = hillHminusPeriodMatrix C N q m n ∧
          (S q (lp.single 2 n 1)) m = hillHminusTwoWeightedPeriodMatrix C N q m n) ∧
        (∀ q ∈ V, ∀ m n : ℤ,
          NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 n 1)) m =
            NLS.Coeff.positiveIndexWeight n^2*(Q q (lp.single 2 n 1)) m) ∧
        ∃ A : ℝ, HillHminusUniformPeriodData C N V A := by
  obtain ⟨C,N,W,T,R,hN,hW,h0W,hTa,hRa,hT0,hR0,hinv,hentry,A,D⟩ :=
    exists_hillHminus_analytic_period_inverse
  obtain ⟨S,hSa,_,hSentry,hS0⟩ := D.exists_twoWeighted_period_operator
  obtain ⟨V,Q,hVW,hV,h0V,hQa,hQ0,hQinv⟩ :=
    NLS.ComplexAnalysis.exists_analytic_operator_inverse_near_zero S W hW h0W hSa hS0
  refine ⟨C,N,V,T,R,S,Q,hN,hV,h0V,hTa.mono hVW,hRa.mono hVW,hSa.mono hVW,hQa,
    hT0,hR0,hS0,hQ0,?_,?_,?_,A,D.mono hVW hV h0V⟩
  · intro q hq
    exact ⟨(hinv q (hVW hq)).1,(hinv q (hVW hq)).2.1,
      (hQinv q hq).1,(hQinv q hq).2.1,(hinv q (hVW hq)).2.2,(hQinv q hq).2.2⟩
  · intro q hq m n
    exact ⟨hentry q (hVW hq) m n,hSentry q (hVW hq) m n⟩
  intro q hq m n
  exact hillHminus_inverse_twoWeight_entries C N q (T q) (S q) (R q) (Q q)
    (hentry q (hVW hq)) (hSentry q (hVW hq)) (hinv q (hVW hq)).2.1 (hQinv q hq).1 m n

end NLS.KdV
