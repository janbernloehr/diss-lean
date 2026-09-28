import NLS.SequenceSpaces.DeletedJacobianSymbol

/-!
# Invertibility from a nonzero finite head and separated tail

A diagonal symbol with nonzero retained entries and a uniform lower
bound outside a finite set is globally bounded away from zero. This
is the final diagonal-operator argument needed in Lemma 12.6 once the
psi estimates supply the corresponding spectral hypotheses.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem exists_positive_lowerBound_on_finset (n : ℤ)
    (d : Coeff ⊤) (s : Finset ℤ)
    (hno : ∀ m ∈ s, m ≠ n → d m ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ m ∈ s, m ≠ n → c ≤ ‖d m‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1,by norm_num,?_⟩
    simp
  | @insert m s hm ih =>
    have hs : ∀ k ∈ s, k ≠ n → d k ≠ 0 := by
      intro k hk hkn
      exact hno k (Finset.mem_insert_of_mem hk) hkn
    obtain ⟨c,hc,hl⟩ := ih hs
    by_cases hmn : m = n
    · refine ⟨c,hc,?_⟩
      intro k hk hkn
      rcases Finset.mem_insert.mp hk with rfl | hks
      · exact False.elim (hkn hmn)
      · exact hl k hks hkn
    · let c' : ℝ := min c ‖d m‖
      have hdpos : 0 < ‖d m‖ := norm_pos_iff.mpr
        (hno m (Finset.mem_insert_self m s) hmn)
      refine ⟨c',lt_min hc hdpos,?_⟩
      intro k hk hkn
      rcases Finset.mem_insert.mp hk with rfl | hks
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hl k hks hkn)

/-- A nonzero diagonal with a uniformly separated two-sided tail is
bounded away from zero on every retained coordinate. -/
theorem exists_deletedSymbol_uniformLowerBound (n : ℤ)
    (d : Coeff ⊤) (K : ℕ)
    (hno : ∀ m : ℤ, m ≠ n → d m ≠ 0)
    (htail : ∀ m : ℤ, m ≠ n → K ≤ m.natAbs → 1 ≤ ‖d m‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℤ, m ≠ n → c ≤ ‖d m‖ := by
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  obtain ⟨c,hc,hl⟩ := exists_positive_lowerBound_on_finset n d s
    (by intro m hm hmn; exact hno m hmn)
  refine ⟨min 1 c,lt_min (by norm_num) hc,?_⟩
  intro m hmn
  by_cases hm : K ≤ m.natAbs
  · exact (min_le_left _ _).trans (htail m hmn hm)
  · have hms : m ∈ s := by
      simp only [s,Finset.mem_Icc]
      omega
    exact (min_le_right _ _).trans (hl m hms hmn)

/-- Under the finite-head and tail lower-bound hypotheses, the
canonical diagonal part of a deleted Jacobian is a Banach-space
isomorphism. -/
theorem deletedJacobianDiagonal_bijective_of_eventually_one_le
    (n : ℤ) (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (K : ℕ)
    (hno : ∀ m : ℤ, m ≠ n →
      deletedJacobianDiagonalSymbol n Q m ≠ 0)
    (htail : ∀ m : ℤ, m ≠ n → K ≤ m.natAbs →
      1 ≤ ‖deletedJacobianDiagonalSymbol n Q m‖) :
    Function.Bijective
      (deletedMultiplierCLM (p := p) n
        (deletedJacobianDiagonalSymbol n Q)) := by
  obtain ⟨c,hc,hlower⟩ :=
    exists_deletedSymbol_uniformLowerBound n
      (deletedJacobianDiagonalSymbol n Q) K hno htail
  exact (deletedMultiplierEquivOfLowerBound (p := p) n
    (deletedJacobianDiagonalSymbol n Q) c hc hlower).bijective

end NLS.Coeff
