import NLS.ZakharovShabat.SourcePrimitivePowerComplexBound

/-! # Lemma 21.1: analytic primitive-power moments

The actual contour moments satisfy all five assertions on a common
complex source neighborhood. The size estimate is uniform over every
index, rather than only the sufficiently distant indices.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All of Lemma 21.1 for the actual primitive and action constructions. -/
theorem exists_sourcePrimitivePower_lemma21_1 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W U : Set (CoeffPair p), IsOpen W ∧ IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      ∃ A : SourcePrimitivePowerAtlas hp hp1 W, U ⊆ A.domain ∧
        (∀ n m, AnalyticOnNhd ℂ (A.moment n m) U) ∧
        (∀ ψ ∈ U, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
          sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
          ∀ n m, A.moment n m ψ = sourcePrimitivePowerCircle hp hp1 W n m ψ (c n) (R n)) ∧
        (∀ ψ ∈ U, ∀ n m, A.moment n (2*m) ψ = 0) ∧
        (∀ φ ∈ U, ∃ r : ℝ, 0 < r ∧ ball φ r ⊆ U ∧ ∃ B : ℝ, 0 < B ∧
          ∀ ψ ∈ ball φ r, ∀ (n : ℤ) (m : ℕ), ‖A.moment n m ψ‖ ≤ B^m *
            ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖^(m+1)) ∧
        (∀ ψ ∈ U, ∀ n,
          canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
          ∀ m, A.moment n m ψ = 0) ∧
        (∀ φ : realTypeSourceSubmodule p, ∀ n m,
          0 ≤ (A.moment n m φ.val).re ∧ (A.moment n m φ.val).im = 0) ∧
        (∀ φ : realTypeSourceSubmodule p, ∀ n m,
          A.moment n (2*m+1) φ.val = 0 ↔
            canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0) ∧
        (∀ n, EqOn (A.moment n 1) (sourceComplexAction hp hp1 n) U) := by
  obtain ⟨W,hW,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas hp hp1
  obtain ⟨U,hU,hconn,hreal,hsub,hbound⟩ := A.exists_almostReal_all_moments_power_bound
  exact ⟨W,U,hW,hU,hconn,hreal,A,hsub,
    fun n m => (A.analytic_moment n m).mono hsub,
    fun ψ hψ => A.circle_representation ψ (hsub hψ),
    fun ψ hψ => A.moment_even ψ (hsub hψ),hbound,
    fun ψ hψ => A.moment_of_collapsed ψ (hsub hψ),
    A.real_moment_nonneg,A.real_odd_moment_eq_zero_iff,
    fun n => (A.moment_one n).mono hsub⟩

end NLS.ZakharovShabat
