import NLS.ZakharovShabat.RealPeriodicProductDerivative
import NLS.ZakharovShabat.UniformCriticalCounts

/-!
# Real-type discriminant critical points and Lemma 8.3

Differentiating the exact full-product identity transfers the real-rooted
limit theorem to the discriminant. Together with the locally uniform counts,
this proves the counting, exhaustion, and reality assertions of Lemma 8.3.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The derivative of the full product is twice the discriminant times its derivative. -/
theorem deriv_canonicalPeriodic_eq_discriminant (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    deriv (canonicalPeriodicProduct hp φ) z =
      2*canonicalDiscriminant hp φ z*deriv (canonicalDiscriminant hp φ) z := by
  have he : canonicalPeriodicProduct hp φ = (fun w => (canonicalDiscriminant hp φ w)^2-4) :=
    funext (canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 φ hφ)
  rw [he, deriv_sub_const, deriv_fun_pow
    (analyticOnNhd_canonicalDiscriminant hp hp1 φ hφ z (mem_univ z)).differentiableAt]
  norm_num

/-- Every discriminant critical point of an even real-type potential is real. -/
theorem discriminant_critical_im_eq_zero_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hφ : IsRealType φ)
    {z : ℂ} (hz : deriv (canonicalDiscriminant hp φ) z = 0) : z.im = 0 := by
  by_contra him
  apply deriv_canonicalPeriodic_ne_zero_of_realType hp hp1 φ hφ him
  rw [deriv_canonicalPeriodic_eq_discriminant hp hp1 φ heven, hz, mul_zero]

/-- The discriminant derivative of an even real-type potential is nonzero off the real axis. -/
theorem discriminant_derivative_ne_zero_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hφ : IsRealType φ)
    {z : ℂ} (hz : z.im ≠ 0) : deriv (canonicalDiscriminant hp φ) z ≠ 0 :=
  fun h => hz (discriminant_critical_im_eq_zero_of_realType hp hp1 φ heven hφ h)

/-- Lemma 8.3: one locally uniform cutoff gives counts and exhaustion, and real-type critical points are real. -/
theorem exists_uniform_discriminant_critical_distribution_with_reality (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 →
        (∀ n : ℤ, N < n.natAbs → ∃ x ∈ ball ((Real.pi : ℂ)*n) r,
          deriv (canonicalDiscriminant hp ψ) x = 0 ∧
          analyticOrderAt (deriv (canonicalDiscriminant hp ψ)) x = 1 ∧
          ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r, deriv (canonicalDiscriminant hp ψ) z = 0 ↔ z = x) ∧
        (∀ K : ℕ, N ≤ K →
          analyticZeroCount (deriv (canonicalDiscriminant hp ψ)) (closedBall 0 (centralCircleRadius K)) = 2*K+1 ∧
          ∀ z ∈ sphere 0 (centralCircleRadius K), deriv (canonicalDiscriminant hp ψ) z ≠ 0) ∧
        (∀ K : ℕ, N ≤ K → ∀ z : ℂ, deriv (canonicalDiscriminant hp ψ) z = 0 →
          z ∈ ball 0 (centralCircleRadius K) ∨ ∃ n : ℤ, K < n.natAbs ∧ z ∈ ball ((Real.pi : ℂ)*n) r) ∧
        (IsRealType ψ → ∀ z : ℂ, deriv (canonicalDiscriminant hp ψ) z = 0 → z.im = 0) := by
  obtain ⟨N, hN, U, ho, hconv, hφ, h0, hdata⟩ :=
    exists_uniform_discriminant_critical_distribution hp hp1 φ hr hrπ
  refine ⟨N, hN, U, ho, hconv, hφ, h0, ?_⟩
  intro ψ hψ heven
  obtain ⟨hd, hc, he⟩ := hdata ψ hψ heven
  exact ⟨hd, hc, he, fun hreal z hz => discriminant_critical_im_eq_zero_of_realType hp hp1 ψ heven hreal hz⟩

end NLS.ZakharovShabat
