import NLS.SequenceSpaces.SignChange

/-! # Complex sign invariance from real quadratic action invariance

On a complex ball with real center, holomorphic maps invariant under
real action fibers are invariant under every coordinate sign change
fixing the center. The sign selection can have infinite support.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A real sign symmetry extends throughout an invariant complex ball. -/
theorem eqOn_pairSignChange_of_real_agreement
    (f : (Coeff p × Coeff p) → F) (c : Coeff p × Coeff p) (r : ℝ) (hr : 0 < r)
    (hcr : c ∈ realPairLocus p) (hf : AnalyticOnNhd ℂ f (ball c r))
    (e d : ℤ → Bool) (hfix : pairSignChange e d c = c)
    (he : ∀ z ∈ ball c r, z ∈ realPairLocus p → f (pairSignChange e d z) = f z) :
    EqOn (f ∘ pairSignChange e d) f (ball c r) := by
  have hg : AnalyticOnNhd ℂ (f ∘ pairSignChange e d) (ball c r) := by
    intro z hz
    exact (hf _ ((pairSignChange_mem_ball e d c z hfix r).mpr hz)).comp
      ((pairSignChange e d).analyticAt z)
  exact eqOn_of_realPair_agreement _ _ _ isOpen_ball (convex_ball c r) c (mem_ball_self hr) hcr
    hg.differentiableOn hf.differentiableOn he

/-- Invariance on real quadratic action fibers supplies every complex
sign symmetry that fixes the ball's center. -/
theorem eqOn_pairSignChange_of_real_action_invariance
    (f : (Coeff p × Coeff p) → F) (c : Coeff p × Coeff p) (r : ℝ) (hr : 0 < r)
    (hcr : c ∈ realPairLocus p) (hf : AnalyticOnNhd ℂ f (ball c r))
    (hinv : ∀ z ∈ ball c r, ∀ w ∈ ball c r,
      z ∈ realPairLocus p → w ∈ realPairLocus p →
      (∀ n, w.1 n ^ 2+w.2 n ^ 2 = z.1 n ^ 2+z.2 n ^ 2) → f w = f z)
    (e d : ℤ → Bool) (hfix : pairSignChange e d c = c) :
    EqOn (f ∘ pairSignChange e d) f (ball c r) := by
  apply eqOn_pairSignChange_of_real_agreement f c r hr hcr hf e d hfix
  intro z hz hzr
  exact hinv z hz _ ((pairSignChange_mem_ball e d c z hfix r).mpr hz)
    hzr (pairSignChange_mem_realPairLocus e d z hzr) (pairSignChange_action e d z)

omit [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] in
/-- Tail sign invariance removes every coordinatewise square-root choice
when the finite head is kept fixed. No coordinate is required to be nonzero. -/
theorem eq_of_coordinate_squares_of_eq_head
    (f : (Coeff p × Coeff p) → F) (S : Finset ℤ) (V : Set (Coeff p × Coeff p))
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (z w : Coeff p × Coeff p) (hz : z ∈ V)
    (hhead : ∀ n ∈ S, z.1 n = w.1 n ∧ z.2 n = w.2 n)
    (hsq : ∀ n, z.1 n^2 = w.1 n^2 ∧ z.2 n^2 = w.2 n^2) : f w = f z := by
  obtain ⟨e,he,hez⟩ := exists_signChange_of_sq_eq_on_complement S z.1 w.1
    (fun n => (hsq n).1) (fun n hn => (hhead n hn).1)
  obtain ⟨d,hd,hdz⟩ := exists_signChange_of_sq_eq_on_complement S z.2 w.2
    (fun n => (hsq n).2) (fun n hn => (hhead n hn).2)
  have heq : pairSignChange e d z = w := Prod.ext hez hdz
  simpa only [heq] using hinv e d he hd z hz

end NLS.Coeff
