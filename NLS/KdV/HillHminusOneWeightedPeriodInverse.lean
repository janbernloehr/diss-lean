import NLS.KdV.HillHminusOneWeightedPeriodOperator
import NLS.SequenceSpaces.DiagonalIntertwining
import NLS.ComplexAnalysis.AnalyticOperatorInverse

/-! # Compatible weighted and unweighted Hill period inverses

The bounded reciprocal diagonal intertwines the two actual period maps.
Their constructed analytic inverses therefore give exactly compatible
columns. In particular the original inverse columns have one index weight
in l2, rather than merely coordinatewise decay.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

theorem hillHminus_period_weight_intertwine (C : HillHminusMiuraChart) (N : ℕ) (q : PeriodOneHminusOne)
    (T S : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)
    (hT : ∀ m n : ℤ, (T (lp.single 2 n 1)) m = hillHminusPeriodMatrix C N q m n)
    (hS : ∀ m n : ℤ, (S (lp.single 2 n 1)) m = hillHminusWeightedPeriodMatrix C N q m n) :
    T.comp (NLS.Coeff.multiplierCLM NLS.Coeff.positiveIndexReciprocal) =
      (NLS.Coeff.multiplierCLM NLS.Coeff.positiveIndexReciprocal).comp S := by
  apply NLS.Coeff.intertwine_diagonal_of_entries (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro m n
  rw [hT,hS,hillHminusWeightedPeriodMatrix,NLS.Coeff.positiveIndexReciprocal_apply,
    NLS.Coeff.positiveIndexReciprocal_apply]
  field_simp [NLS.Coeff.positiveIndexWeight_ne_zero]

theorem hillHminus_inverse_weight_entries (C : HillHminusMiuraChart) (N : ℕ) (q : PeriodOneHminusOne)
    (T S R Q : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)
    (hT : ∀ m n : ℤ, (T (lp.single 2 n 1)) m = hillHminusPeriodMatrix C N q m n)
    (hS : ∀ m n : ℤ, (S (lp.single 2 n 1)) m = hillHminusWeightedPeriodMatrix C N q m n)
    (hRT : R.comp T = ContinuousLinearMap.id ℂ (NLS.Coeff 2))
    (hSQ : S.comp Q = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (m n : ℤ) :
    NLS.Coeff.positiveIndexWeight m*(R (lp.single 2 n 1)) m =
      NLS.Coeff.positiveIndexWeight n*(Q (lp.single 2 n 1)) m := by
  have he := NLS.Coeff.inverse_diagonal_entries NLS.Coeff.positiveIndexReciprocal T S R Q
    (hillHminus_period_weight_intertwine C N q T S hT hS) hRT hSQ m n
  simp only [NLS.Coeff.positiveIndexReciprocal_apply] at he
  field_simp [NLS.Coeff.positiveIndexWeight_ne_zero] at he
  simpa only [mul_comm] using he

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

/-- The SAME actual unweighted normalization inverse has one-weight
columns supplied by ONE analytic bounded operator, with its full norm bound.
Individual column bounds are not used in place of an operator estimate. -/
theorem exists_weighted_inverse_for_normalization
    (T R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hT : ∀ q∈V, ∀ m n : ℤ, (T q (lp.single 2 n 1)) m=hillHminusPeriodMatrix C N q m n)
    (hRT : ∀ q∈V, (R q).comp (T q)=ContinuousLinearMap.id ℂ (NLS.Coeff 2)) :
    ∃ U : Set PeriodOneHminusOne, ∃ Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
      U⊆V ∧ IsOpen U ∧ (0 : PeriodOneHminusOne)∈U ∧ AnalyticOnNhd ℂ Q U ∧
      Q 0=ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
      (∀ q∈U, ‖Q q‖≤2) ∧ ∀ q∈U, ∀ m n : ℤ,
        NLS.Coeff.positiveIndexWeight m*(R q (lp.single 2 n 1)) m=
          NLS.Coeff.positiveIndexWeight n*(Q q (lp.single 2 n 1)) m := by
  obtain ⟨S,hSa,_,hSentry,hS0⟩ := D.exists_weighted_period_operator
  obtain ⟨U,Q,hUV,hU,h0U,hQa,hQ0,hQinv⟩ :=
    NLS.ComplexAnalysis.exists_analytic_operator_inverse_near_zero S V D.isOpen D.zero_mem hSa hS0
  refine ⟨U,Q,hUV,hU,h0U,hQa,hQ0,(fun q hq => (hQinv q hq).2.2),?_⟩
  intro q hq m n
  exact hillHminus_inverse_weight_entries C N q (T q) (S q) (R q) (Q q)
    (hT q (hUV hq)) (hSentry q (hUV hq)) (hRT q (hUV hq)) (hQinv q hq).1 m n

end HillHminusUniformPeriodData
end NLS.KdV
