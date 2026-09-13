import NLS.SequenceSpaces.IteratedRowTesting

/-!
# Disjoint regions for absolutely convergent double series

The first far index, the second far index with the first near, and the two
near indices partition the full product lattice without double counting.
-/

noncomputable section
namespace NLS.Coeff

/-- The first reciprocal index is distant, including the cutoff boundary. -/
def doubleFarLeft (M : ℕ) (F : ℤ × ℤ → ℂ) (jk : ℤ × ℤ) : ℂ :=
  if M ≤ jk.1.natAbs then F jk else 0

/-- The second reciprocal index is distant and the first lies strictly inside the cutoff. -/
def doubleFarRight (M : ℕ) (F : ℤ × ℤ → ℂ) (jk : ℤ × ℤ) : ℂ :=
  if jk.1.natAbs < M ∧ M ≤ jk.2.natAbs then F jk else 0

/-- Both reciprocal indices lie strictly inside the cutoff. -/
def doubleNear (M : ℕ) (F : ℤ × ℤ → ℂ) (jk : ℤ × ℤ) : ℂ :=
  if jk.1.natAbs < M ∧ jk.2.natAbs < M then F jk else 0

/-- These three regions are an exact disjoint partition. -/
theorem double_region_partition (M : ℕ) (F : ℤ × ℤ → ℂ) :
    F = doubleFarLeft M F + doubleFarRight M F + doubleNear M F := by
  funext jk
  by_cases hj : M ≤ jk.1.natAbs <;> by_cases hk : M ≤ jk.2.natAbs <;>
    simp [doubleFarLeft, doubleFarRight, doubleNear, hj, hk, Nat.lt_of_not_ge, Nat.not_lt.mpr]

/-- Restricting to each region preserves joint absolute convergence. -/
theorem summable_norm_double_regions (M : ℕ) {F : ℤ × ℤ → ℂ} (hF : Summable (fun jk => ‖F jk‖)) :
    Summable (fun jk => ‖doubleFarLeft M F jk‖) ∧
      Summable (fun jk => ‖doubleFarRight M F jk‖) ∧ Summable (fun jk => ‖doubleNear M F jk‖) := by
  refine ⟨hF.of_nonneg_of_le (fun _ => norm_nonneg _) ?_,
    hF.of_nonneg_of_le (fun _ => norm_nonneg _) ?_,
    hF.of_nonneg_of_le (fun _ => norm_nonneg _) ?_⟩ <;> intro jk
  · unfold doubleFarLeft; split_ifs <;> simp
  · unfold doubleFarRight; split_ifs <;> simp
  · unfold doubleNear; split_ifs <;> simp

/-- The actual double-series sum decomposes into its three absolutely convergent regions. -/
theorem tsum_double_regions (M : ℕ) {F : ℤ × ℤ → ℂ} (hF : Summable (fun jk => ‖F jk‖)) :
    (∑' jk, F jk) = (∑' jk, doubleFarLeft M F jk) +
      (∑' jk, doubleFarRight M F jk) + (∑' jk, doubleNear M F jk) := by
  obtain ⟨h₁,h₂,h₃⟩ := summable_norm_double_regions M hF
  calc
    _ = ∑' jk, (doubleFarLeft M F jk + doubleFarRight M F jk + doubleNear M F jk) := by
      exact congrArg (fun G : ℤ × ℤ → ℂ => ∑' jk, G jk) (double_region_partition M F)
    _ = _ := by rw [(h₁.of_norm.add h₂.of_norm).tsum_add h₃.of_norm, h₁.of_norm.tsum_add h₂.of_norm]

/-- The triangle inequality is valid for the exact region decomposition. -/
theorem norm_tsum_double_regions_le (M : ℕ) {F : ℤ × ℤ → ℂ} (hF : Summable (fun jk => ‖F jk‖)) :
    ‖∑' jk, F jk‖ ≤ ‖∑' jk, doubleFarLeft M F jk‖ +
      ‖∑' jk, doubleFarRight M F jk‖ + ‖∑' jk, doubleNear M F jk‖ := by
  rw [tsum_double_regions M hF]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

end NLS.Coeff
