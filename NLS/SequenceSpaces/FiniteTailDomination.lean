import NLS.SequenceSpaces.FiniteModification

/-! Norm domination outside a finite signed block transfers membership
at EVERY sequence exponent, without a norm bound on the finite correction. -/
noncomputable section
open scoped ENNReal
namespace NLS

/-- A constant norm majorant on both signed tails transfers lp membership.
The exponent may be infinite, and the finite central values are unrestricted. -/
theorem memlp_of_natAbs_tail_norm_le {p : ℝ≥0∞} (f g : ℤ → ℂ)
    (hg : Memℓp g p) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℤ, N ≤ k.natAbs → ‖f k‖ ≤ C*‖g k‖) : Memℓp f p := by
  let t : ℤ → ℂ := fun k => if N ≤ k.natAbs then f k else 0
  have ht : Memℓp t p := by
    have hmajor : Memℓp (fun k : ℤ => C*‖g k‖) p := hg.norm.const_mul C
    apply hmajor.mono
    intro k
    change ‖t k‖ ≤ C*‖g k‖
    dsimp [t]
    split_ifs with hk
    · exact hb k hk
    · simpa only [norm_zero] using mul_nonneg hC (norm_nonneg (g k))
  apply memℓp_of_eq_outside_finset ht (Finset.Icc (-(N:ℤ)) N)
  intro k hk
  have hkn : N ≤ k.natAbs := by simp only [Finset.mem_Icc] at hk; omega
  simp only [t,if_pos hkn]

end NLS
