import NLS.SequenceSpaces.TailSquareDescentAnalytic

/-! # Scalar analytic descent through squared tail coordinates

Embedding a scalar in a single ℓ¹ coordinate and evaluating it back
transfers the established Banach-space descent theorem to scalar maps.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- Scalar sign-invariant analytic maps descend analytically in the full
half-exponent norm, including at zero tail entries. -/
theorem analyticOnNhd_scalar_tailSquareDescent (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → ℂ) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z) :
    AnalyticOnNhd ℂ (tailSquareDescent (q := q) S f V) (pairMixedSquare S '' V) := by
  let E : ℂ →L[ℂ] Coeff 1 := lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 1 0
  let L : Coeff 1 →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 0
  have hE : AnalyticOnNhd ℂ (E ∘ f) V := fun z hz => (E.analyticAt (f z)).comp (hf z hz)
  have hEi : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, (E ∘ f) (pairSignChange e d z) = (E ∘ f) z := by
    intro e d he hd z hz
    exact congrArg E (hinv e d he hd z hz)
  have ha := analyticOnNhd_tailSquareDescent (q := q) hp S (E ∘ f) V hV hE hEi
  have hopen := isOpenMap_pairMixedSquare (q := q) hp S V hV
  have heq : EqOn (fun b => L (tailSquareDescent (q := q) S (E ∘ f) V b))
      (tailSquareDescent (q := q) S f V) (pairMixedSquare S '' V) := by
    rintro b ⟨z,hz,rfl⟩
    dsimp only
    rw [tailSquareDescent_apply S (E ∘ f) V hEi z hz,tailSquareDescent_apply S f V hinv z hz]
    change (lp.single 1 (0:ℤ) (f z) : Coeff 1) 0 = f z
    simp
  intro b hb
  exact ((L.analyticAt _).comp (ha b hb)).congr
    (Filter.eventuallyEq_of_mem (hopen.mem_nhds hb) (fun c hc => heq hc))

end NLS.Coeff
