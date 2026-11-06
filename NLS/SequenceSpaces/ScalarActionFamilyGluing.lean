import NLS.SequenceSpaces.NonnegativeActionGluing

/-! # Simultaneous scalar gluing on action balls

The union of the local balls is chosen before the scalar-family index.
Nonnegative overlap agreement determines every complex overlap, so all
components glue on one common open set. Every local bound is preserved.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- An arbitrary scalar family glues on the same union of action balls. -/
theorem exists_analytic_scalar_family_gluing {α ι : Type*} (hp : p ≠ ⊤)
    (a : α → Coeff q) (r : α → ℝ) (f : α → ι → Coeff q → ℂ)
    (ha : ∀ j, a j ∈ nonnegativeLocus q)
    (hf : ∀ j i, AnalyticOnNhd ℂ (f j i) (ball (a j) (r j)))
    (he : ∀ j k i b, b ∈ ball (a j) (r j) ∩ ball (a k) (r k) →
      b ∈ nonnegativeLocus q → f j i b = f k i b) :
    ∃ G : ι → Coeff q → ℂ,
      (∀ i, AnalyticOnNhd ℂ (G i) (⋃ j, ball (a j) (r j))) ∧
      (∀ j i, EqOn (G i) (f j i) (ball (a j) (r j))) ∧
      ∀ H : ι → Coeff q → ℂ, (∀ j i, EqOn (H i) (f j i) (ball (a j) (r j))) →
        ∀ i, EqOn (H i) (G i) (⋃ j, ball (a j) (r j)) := by
  classical
  have hcomponent (i : ι) := exists_analyticOnNhd_gluing_nonnegativeActions hp a r
    (fun j => f j i) ha (fun j => hf j i) (fun j k => he j k i)
  choose G hG hlocal huniq using hcomponent
  exact ⟨G,hG,(fun j i => hlocal i j),fun H hH i => huniq i (H i) (fun j => hH j i)⟩

/-- A bound on any original ball holds on that whole ball after gluing,
with its original function index and constant. -/
theorem exists_analytic_scalar_family_gluing_with_bounds {α ι : Type*} (hp : p ≠ ⊤)
    (a : α → Coeff q) (r : α → ℝ) (f : α → ι → Coeff q → ℂ)
    (ha : ∀ j, a j ∈ nonnegativeLocus q)
    (hf : ∀ j i, AnalyticOnNhd ℂ (f j i) (ball (a j) (r j)))
    (he : ∀ j k i b, b ∈ ball (a j) (r j) ∩ ball (a k) (r k) →
      b ∈ nonnegativeLocus q → f j i b = f k i b)
    (B : α → ι → Coeff q → ℝ)
    (hbound : ∀ j i b, b ∈ ball (a j) (r j) → ‖f j i b‖ ≤ B j i b) :
    ∃ G : ι → Coeff q → ℂ,
      (∀ i, AnalyticOnNhd ℂ (G i) (⋃ j, ball (a j) (r j))) ∧
      (∀ j i, EqOn (G i) (f j i) (ball (a j) (r j))) ∧
      ∀ j i b, b ∈ ball (a j) (r j) → ‖G i b‖ ≤ B j i b := by
  obtain ⟨G,hG,hlocal,_⟩ := exists_analytic_scalar_family_gluing (q := q) hp a r f ha hf he
  refine ⟨G,hG,hlocal,?_⟩
  intro j i b hb
  rw [hlocal j i hb]
  exact hbound j i b hb

end NLS.Coeff
