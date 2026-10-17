import NLS.SequenceSpaces.TailDiagonalCompact
import NLS.SequenceSpaces.SourceCotangent
import NLS.SequenceSpaces.Reflection

/-! # Compactness from exact signed two-mode rows

Two compact diagonal multipliers reconstruct each scalar output after
reflecting the first source component. This gives a compact pair operator
when all four tail entries vanish. Rows are identified on every input,
so no density of finitely supported sequences is assumed at infinity.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A scalar-output operator with two signed tail modes is compact when both entries vanish. -/
theorem isCompactOperator_of_tail_two_modes
    (T : CoeffPair p →L[ℂ] Coeff p) (K : ℕ)
    (hrow : ∀ n : ℤ, K ≤ n.natAbs → ∀ a : CoeffPair p,
      T a n = a.fst (-n)*T (CoeffPair.inlCLM (lp.single p (-n) 1)) n+
        a.snd n*T (CoeffPair.inrCLM (lp.single p n 1)) n)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ K' : ℕ, ∀ n : ℤ, K' ≤ n.natAbs →
      ‖T (CoeffPair.inlCLM (lp.single p (-n) 1)) n‖ < ε ∧
      ‖T (CoeffPair.inrCLM (lp.single p n 1)) n‖ < ε) : IsCompactOperator T := by
  let A := (T.comp CoeffPair.inlCLM).comp Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap
  let B := T.comp CoeffPair.inrCLM
  have hArow (n : ℤ) (hn : K ≤ n.natAbs) (a : Coeff p) :
      A a n = a n*T (CoeffPair.inlCLM (lp.single p (-n) 1)) n := by
    simpa [A] using hrow n hn (CoeffPair.inlCLM (Coeff.reflection a))
  have hBrow (n : ℤ) (hn : K ≤ n.natAbs) (a : Coeff p) :
      B a n = a n*T (CoeffPair.inrCLM (lp.single p n 1)) n := by
    simpa [B] using hrow n hn (CoeffPair.inrCLM a)
  have hAdiag (n : ℤ) (hn : K ≤ n.natAbs) :
      A (lp.single p n 1) n = T (CoeffPair.inlCLM (lp.single p (-n) 1)) n := by
    simpa using hArow n hn (lp.single p n 1)
  have hBdiag (n : ℤ) (hn : K ≤ n.natAbs) :
      B (lp.single p n 1) n = T (CoeffPair.inrCLM (lp.single p n 1)) n := by
    simpa using hBrow n hn (lp.single p n 1)
  have hAc : IsCompactOperator A := by
    apply Coeff.isCompactOperator_of_tail_diagonal A K
    · intro n hn a
      rw [hArow n hn a,hAdiag n hn]
    · intro ε hε
      obtain ⟨K',hK'⟩ := htail ε hε
      refine ⟨max K K',fun n hn => ?_⟩
      rw [hAdiag n (by omega)]
      exact (hK' n (by omega)).1
  have hBc : IsCompactOperator B := by
    apply Coeff.isCompactOperator_of_tail_diagonal B K
    · intro n hn a
      rw [hBrow n hn a,hBdiag n hn]
    · intro ε hε
      obtain ⟨K',hK'⟩ := htail ε hε
      refine ⟨max K K',fun n hn => ?_⟩
      rw [hBdiag n (by omega)]
      exact (hK' n (by omega)).2
  let P := Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp (CoeffPair.toMax p).toContinuousLinearMap)
  let Q := (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp (CoeffPair.toMax p).toContinuousLinearMap
  have he : T = A.comp P+B.comp Q := by
    ext a n
    change T a n = (T (CoeffPair.inlCLM (Coeff.reflection (Coeff.reflection a.fst)))) n+
      (T (CoeffPair.inrCLM a.snd)) n
    rw [Coeff.reflection_reflection]
    have ha : a = CoeffPair.inlCLM a.fst+CoeffPair.inrCLM a.snd := by
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> simp
    nth_rw 1 [ha]
    simp only [map_add,lp.coeFn_add,Pi.add_apply]
  rw [he]
  exact (hAc.comp_clm P).add (hBc.comp_clm Q)
end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Exact signed tail blocks with all four entries vanishing give a compact pair operator. -/
theorem isCompactOperator_of_tail_signed_blocks
    (T : CoeffPair p →L[ℂ] (Coeff p × Coeff p)) (K : ℕ)
    (hrow : ∀ n : ℤ, K ≤ n.natAbs → ∀ a : CoeffPair p,
      (T a).1 n = a.fst (-n)*(T (CoeffPair.inlCLM (lp.single p (-n) 1))).1 n+
        a.snd n*(T (CoeffPair.inrCLM (lp.single p n 1))).1 n ∧
      (T a).2 n = a.fst (-n)*(T (CoeffPair.inlCLM (lp.single p (-n) 1))).2 n+
        a.snd n*(T (CoeffPair.inrCLM (lp.single p n 1))).2 n)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ K' : ℕ, ∀ n : ℤ, K' ≤ n.natAbs →
      ‖(T (CoeffPair.inlCLM (lp.single p (-n) 1))).1 n‖ < ε ∧
      ‖(T (CoeffPair.inlCLM (lp.single p (-n) 1))).2 n‖ < ε ∧
      ‖(T (CoeffPair.inrCLM (lp.single p n 1))).1 n‖ < ε ∧
      ‖(T (CoeffPair.inrCLM (lp.single p n 1))).2 n‖ < ε) : IsCompactOperator T := by
  let A := (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp T
  let B := (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp T
  have hA : IsCompactOperator A := by
    apply isCompactOperator_of_tail_two_modes A K (fun n hn a => (hrow n hn a).1)
    intro ε hε
    obtain ⟨K',hK'⟩ := htail ε hε
    exact ⟨K',fun n hn => ⟨(hK' n hn).1,(hK' n hn).2.2.1⟩⟩
  have hB : IsCompactOperator B := by
    apply isCompactOperator_of_tail_two_modes B K (fun n hn a => (hrow n hn a).2)
    intro ε hε
    obtain ⟨K',hK'⟩ := htail ε hε
    exact ⟨K',fun n hn => ⟨(hK' n hn).2.1,(hK' n hn).2.2.2⟩⟩
  have he : T = (ContinuousLinearMap.inl ℂ (Coeff p) (Coeff p)).comp A+
      (ContinuousLinearMap.inr ℂ (Coeff p) (Coeff p)).comp B := by
    apply ContinuousLinearMap.ext
    intro a
    apply Prod.ext <;> simp [A,B]
  rw [he]
  exact (hA.clm_comp (ContinuousLinearMap.inl ℂ (Coeff p) (Coeff p))).add
    (hB.clm_comp (ContinuousLinearMap.inr ℂ (Coeff p) (Coeff p)))
end NLS.ZakharovShabat
