import NLS.SequenceSpaces.FiniteExponentTail
import NLS.ZakharovShabat.SourceSquaredGapReciprocalRows

/-!
# Decay of the physical squared-gap reciprocal rows

The row sums from Lemma 10.8 form an `ℓ^(p/2)` sequence. Their
coordinates therefore vanish at both ends of the integer lattice,
even when `p/2 < 1`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For a fixed source, the physical off-diagonal squared-gap row sum
decays to zero as the omitted index tends to either infinity. -/
theorem exists_sourceSquaredGapPhysicalRows_natAbs_lt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs →
      (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) < δ := by
  obtain ⟨S,hS,_⟩ := exists_sourceSquaredGapPhysicalRows hp hp1 ψ
  have hpr : 1 < p.toReal :=
    (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hr : 0 < (ENNReal.ofReal (p.toReal/2)).toReal := by
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ p.toReal/2)]
    linarith
  obtain ⟨K,hK⟩ := Coeff.exists_natAbs_norm_lt hr S hδ
  refine ⟨K,?_⟩
  intro n hn
  have hrow_nonneg : 0 ≤
      ∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m := by
    apply tsum_nonneg
    intro m
    unfold sourceSquaredGapReciprocalTerm
    split_ifs
    · rfl
    · positivity
  have hnorm : ‖S n‖ =
      ∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m := by
    rw [(hS n).2, Complex.norm_real, Real.norm_of_nonneg hrow_nonneg]
  rw [← hnorm]
  exact hK n hn

/-- The full physical row is eventually small enough to put every
off-diagonal gap radicand in the half-unit ball. -/
theorem exists_sourceSquaredGapPhysicalRows_half_unit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs →
      (C^2/4) *
        (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤ 1/2 := by
  have hCpos : 0 < C := by linarith
  have hC2 : 0 < C^2 := sq_pos_of_pos hCpos
  obtain ⟨K,hK⟩ := exists_sourceSquaredGapPhysicalRows_natAbs_lt
    hp hp1 ψ (show 0 < 2/C^2 by positivity)
  refine ⟨K,?_⟩
  intro n hn
  have hlt := hK n hn
  have hmul := (lt_div_iff₀ hC2).mp hlt
  nlinarith

end NLS.ZakharovShabat
