import NLS.SequenceSpaces.PeriodOneMiuraRealLift
import NLS.SequenceSpaces.SobolevSesquilinearPairing
import NLS.ComplexAnalysis.ConjugationRealForm

/-! # Analytic uniqueness on the actual physical H-minus-one real form

Physical reality is conjugate reflection of Fourier coefficients. Its
isometric conjugation gives a contractive real projection, so every
overlap of real-centered complex balls has a real point. Analytic
uniqueness applies to the full complex overlap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal ComplexConjugate
namespace NLS
open NLS.ComplexAnalysis

def periodOneHminusConjugation : PeriodOneHminusOne ≃ₗᵢ⋆[ℂ] PeriodOneHminusOne :=
  WeightedCoeff.sobolevConjugation (-1)

theorem periodOneHminusConjugation_involutive (q : PeriodOneHminusOne) :
    periodOneHminusConjugation (periodOneHminusConjugation q) = q :=
  WeightedCoeff.sobolevConjugation_involutive (-1) q

theorem isRealPeriodOneHminusOne_iff_conjugation_fixed (q : PeriodOneHminusOne) :
    IsRealPeriodOneHminusOne q ↔ periodOneHminusConjugation q = q := by
  constructor
  · intro hq
    exact periodOne_realConjugation_eq_self q hq
  · intro hq k
    have he := congrArg (fun a : PeriodOneHminusOne => a.val (-k)) hq
    dsimp only [periodOneHminusConjugation] at he
    rw [WeightedCoeff.sobolevConjugation_apply] at he
    simpa only [neg_neg,Complex.star_def] using he.symm

theorem isPreconnected_real_periodOneHminus :
    IsPreconnected {q : PeriodOneHminusOne | IsRealPeriodOneHminusOne q} := by
  have he : {q : PeriodOneHminusOne | IsRealPeriodOneHminusOne q} =
      {q | periodOneHminusConjugation q = q} := by
    ext q
    exact isRealPeriodOneHminusOne_iff_conjugation_fixed q
  rw [he]
  exact isPreconnected_fixed_real_form periodOneHminusConjugation periodOneHminusConjugation_involutive

theorem exists_real_mem_periodOneHminus_ball_inter
    (a b : PeriodOneHminusOne) (ha : IsRealPeriodOneHminusOne a) (hb : IsRealPeriodOneHminusOne b)
    (r s : ℝ) (hne : (ball a r ∩ ball b s).Nonempty) :
    ∃ q ∈ ball a r ∩ ball b s, IsRealPeriodOneHminusOne q := by
  obtain ⟨q,hq,hqr⟩ := exists_fixed_mem_ball_inter periodOneHminusConjugation
    periodOneHminusConjugation_involutive a b
    ((isRealPeriodOneHminusOne_iff_conjugation_fixed a).mp ha)
    ((isRealPeriodOneHminusOne_iff_conjugation_fixed b).mp hb) r s hne
  exact ⟨q,hq,(isRealPeriodOneHminusOne_iff_conjugation_fixed q).mpr hqr⟩

theorem analytic_eqOn_of_real_periodOneHminus
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : ∃ q ∈ U, IsRealPeriodOneHminusOne q)
    (f g : PeriodOneHminusOne → ℂ) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ q ∈ U, IsRealPeriodOneHminusOne q → f q = g q) : EqOn f g U := by
  refine analytic_eqOn_of_fixed_real_form periodOneHminusConjugation
    periodOneHminusConjugation_involutive U hU hconn ?_ f g hf hg ?_
  · obtain ⟨q,hq,hqr⟩ := hne
    exact ⟨q,hq,(isRealPeriodOneHminusOne_iff_conjugation_fixed q).mp hqr⟩
  · intro q hq hqr
    exact he q hq ((isRealPeriodOneHminusOne_iff_conjugation_fixed q).mpr hqr)

end NLS
