import NLS.Articles.KdVConvexity.GlobalCanonicalMomentFamily
import NLS.KdV.HillHminusOneIsospectralPeriods

/-! # Global canonical families with actual real isospectral invariance

The global potential-space analytic family retains all local uniform
complex estimates, and equality of the actual entire discriminants fixes
all its real values. Action-fiber invariance still requires a spectral
coordinate realization.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

theorem exists_global_isospectral_canonical_moment_family :
    ∃ Ω : Set PeriodOneHminusOne, IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q} ⊆ Ω ∧
      ∃ A : ℕ+ → ℕ → PeriodOneHminusOne → ℂ, ∃ R : ℕ+ → PeriodOneHminusOne → ℂ,
        (∀ n m, AnalyticOnNhd ℂ (A n m) Ω) ∧ (∀ n, AnalyticOnNhd ℂ (R n) Ω) ∧
        (∀ q : PeriodOneHminusOne, ∀ hq : IsRealPeriodOneHminusOne q, ∀ n : ℕ+,
          (∀ m, A n m q = hillHminusRealGapContourMoment q hq n m) ∧
          R n q = hillHminusRealGapCubicContourMoment q hq n ∧
          0 ≤ (A n 0 q).re ∧ (R n q).re ≤ 0 ∧ (R n q).im = 0 ∧ (R n q = 0 ↔ A n 0 q = 0)) ∧
        (∀ q p : PeriodOneHminusOne, IsRealPeriodOneHminusOne q → IsRealPeriodOneHminusOne p →
          hillHminusDiscriminant q = hillHminusDiscriminant p →
          (∀ n m, A n m q = A n m p) ∧ ∀ n, R n q = R n p) ∧
        ∀ q : PeriodOneHminusOne, IsRealPeriodOneHminusOne q →
          ∃ C : ℝ, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
            0 < C ∧ 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ Ω ∧
            ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ p ∈ V,
              (∀ m, A n m p = hillHminusHighContourMoment (n : ℕ) m p) ∧
              R n p = hillHminusHighCubicContourMoment (n : ℕ) p ∧
              ‖((8*(n : ℕ)*Real.pi : ℝ) : ℂ)*R n p‖ ≤ C*‖A n 0 p‖^2 := by
  obtain ⟨Ω,hΩ,hrealΩ,A,R,hA,hR,hvalues,htail⟩ := exists_global_analytic_canonical_moment_family
  refine ⟨Ω,hΩ,hrealΩ,A,R,hA,hR,hvalues,?_,htail⟩
  intro q p hq hp hD
  have he (n : ℕ+) := hillHminusRealGapContourMoments_eq_of_discriminant_eq q p hq hp hD n
  constructor
  · intro n m
    rw [(hvalues q hq n).1 m,(hvalues p hp n).1 m]
    exact (he n).1 m
  · intro n
    rw [(hvalues q hq n).2.1,(hvalues p hp n).2.1]
    exact (he n).2

end NLS.Articles.KdVConvexity
