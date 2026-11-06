import NLS.KdV.HillHminusOneAnalyticCanonicalPeriods

/-! # One analytic neighborhood for any finite head of actual H^-1 periods

Finite intersection places the neighborhood before every prescribed
index and every polynomial moment. This is the central finite-head input
needed alongside the independently proved common high-index family.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

theorem exists_hillHminus_finite_canonical_period_extensions
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (S : Finset ℕ+) :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ q ∈ W ∧
      ∃ A : ℕ+ → ℕ → PeriodOneHminusOne → ℂ, ∃ R : ℕ+ → PeriodOneHminusOne → ℂ,
        ∀ n ∈ S, (∀ m, AnalyticOnNhd ℂ (A n m) W) ∧ AnalyticOnNhd ℂ (R n) W ∧
          ∀ p ∈ W, ∀ hp : IsRealPeriodOneHminusOne p,
            (∀ m, A n m p = hillHminusRealGapContourMoment p hp n m) ∧
            R n p = hillHminusRealGapCubicContourMoment p hp n := by
  classical
  choose V hV hqV A R hA hR hmatch using fun n : ℕ+ =>
    exists_hillHminus_analytic_canonical_gap_periods q hr n
  let W := ⋂ n ∈ S, V n
  have hW : IsOpen W := isOpen_biInter_finset (fun n _ => hV n)
  have hqW : q ∈ W := by
    simp only [W,mem_iInter]
    exact fun n _ => hqV n
  have hWV (n : ℕ+) (hn : n ∈ S) : W ⊆ V n := by
    intro p hp
    exact mem_iInter.mp (mem_iInter.mp hp n) hn
  refine ⟨W,hW,hqW,A,R,?_⟩
  intro n hn
  exact ⟨fun m => (hA n m).mono (hWV n hn),(hR n).mono (hWV n hn),
    fun p hp hpr => hmatch n p (hWV n hn hp) hpr⟩

end NLS.KdV
