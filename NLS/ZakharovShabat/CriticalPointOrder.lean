import NLS.ZakharovShabat.CentralCriticalReordering

/-!
# Global order of critical roots

Free-disc separation orders all distant roots by their real parts. The
central disc lies between the two distant tails, so sorting its finite
multiset orders the complete sequence lexicographically.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {ξ : ℤ → ℂ}

/-- The central labels' real parts lie between the central radius bounds. -/
theorem CriticalPointLabeling.abs_re_central_le (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (n : ℤ) (hn : n.natAbs ≤ N) : |(ξ n).re| ≤ centralCircleRadius N := by
  have hb : ‖ξ n‖ ≤ centralCircleRadius N := by simpa using h.central_mem n hn
  exact (Complex.abs_re_le_norm _).trans hb

/-- A distant label has real part within a quarter pi of its signed free center. -/
theorem CriticalPointLabeling.abs_re_distant_sub_lt (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (n : ℤ) (hn : N < n.natAbs) : |(ξ n).re-Real.pi*n| < Real.pi/4 := by
  have hb : ‖ξ n-(Real.pi : ℂ)*n‖ < Real.pi/4 := by
    simpa only [mem_ball, dist_eq_norm] using (h.distant n hn).1
  simpa using (Complex.abs_re_le_norm (ξ n-(Real.pi : ℂ)*n)).trans_lt hb

/-- Increasing indices are strictly separated in real part whenever at least one is distant. -/
theorem CriticalPointLabeling.re_lt_of_distant (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (i j : ℤ) (hij : i < j) (hd : N < i.natAbs ∨ N < j.natAbs) : (ξ i).re < (ξ j).re := by
  by_cases hi : i.natAbs ≤ N
  · have hj : N < j.natAbs := hd.resolve_left (by omega)
    have hib := (abs_le.mp (h.abs_re_central_le i hi)).2
    have hjb := (abs_lt.mp (h.abs_re_distant_sub_lt j hj)).1
    have hjN : (N : ℝ)+1 ≤ (j : ℝ) := by
      exact_mod_cast (show (N : ℤ)+1 ≤ j by omega)
    unfold centralCircleRadius at hib
    nlinarith [Real.pi_pos]
  · have hi' : N < i.natAbs := by omega
    have hib := (abs_lt.mp (h.abs_re_distant_sub_lt i hi')).2
    by_cases hj : j.natAbs ≤ N
    · have hjb := (abs_le.mp (h.abs_re_central_le j hj)).1
      have hiN : (i : ℝ) ≤ -(N : ℝ)-1 := by
        exact_mod_cast (show i ≤ -(N : ℤ)-1 by omega)
      unfold centralCircleRadius at hjb
      nlinarith [Real.pi_pos]
    · have hjb := (abs_lt.mp (h.abs_re_distant_sub_lt j (by omega))).1
      have hij' : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
      nlinarith [Real.pi_pos]

/-- Ordering the central labels suffices to order the entire bi-infinite sequence. -/
theorem CriticalPointLabeling.lex_monotone_of_central (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hc : ∀ i : ℤ, i.natAbs ≤ N → ∀ j : ℤ, j.natAbs ≤ N → i ≤ j → complexLexLE (ξ i) (ξ j)) :
    Monotone (fun n => complexLexKey (ξ n)) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · by_cases hi : i.natAbs ≤ N
    · by_cases hj : j.natAbs ≤ N
      · exact hc i hi j hj hij.le
      · exact complexLexLE_of_re_lt (h.re_lt_of_distant i j hij (Or.inr (by omega)))
    · exact complexLexLE_of_re_lt (h.re_lt_of_distant i j hij (Or.inl (by omega)))
  · exact le_rfl

/-- A complete critical sequence can be sorted by changing only its finite central enumeration. -/
theorem CriticalPointLabeling.exists_ordered_relabeling (h : CriticalPointLabeling hp hp1 φ hφ N ξ) :
    ∃ α : ℤ → ℂ, CriticalPointLabeling hp hp1 φ hφ N (spliceCentralRoots N α ξ) ∧
      Monotone (fun n => complexLexKey (spliceCentralRoots N α ξ n)) := by
  obtain ⟨α,hα,hs⟩ := h.exists_ordered_central
  refine ⟨α,hα,hα.lex_monotone_of_central ?_⟩
  intro i hi j hj hij
  simpa only [spliceCentralRoots, if_neg (by omega : ¬N < i.natAbs),
    if_neg (by omega : ¬N < j.natAbs)] using hs i hi j hj hij

end NLS.ZakharovShabat
