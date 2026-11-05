import NLS.SequenceSpaces.WeightedMomentRowBound
import NLS.SequenceSpaces.WeightedRawDomination
import NLS.SequenceSpaces.PositiveScalarExtension
import NLS.SequenceSpaces.SignedSobolevWeight

/-! Actual weighted lp realizations of positive moment series, with
literal coefficients and an explicit all-row norm estimate. -/
noncomputable section
open Set Complex NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem signed_inverse_weight_positive (n : ℕ+) :
    (Weight.signedSobolev (-1) ((n:ℕ):ℤ):ℂ)=((n:ℕ):ℂ)⁻¹ := by
  have hn : (0:ℝ) ≤ (n:ℕ) := by positivity
  have hn1 : (1:ℝ) ≤ (n:ℕ) := by exact_mod_cast n.pos
  simp only [Weight.signedSobolev,Int.cast_natCast,abs_of_nonneg hn,max_eq_right hn1,
    Real.rpow_neg_one,ofReal_inv,ofReal_natCast]

theorem exists_weighted_positive_moment_series (hp : 1 < p) (g : Coeff 2)
    (u : ℕ+ → ℕ+ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ n m : ℕ+, ‖u n m‖ ≤ B*‖g ((m:ℕ):ℤ)‖^2*
      (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) :
    ∃ b : WeightedCoeff (Weight.signedSobolev (-1)) p,
      (∀ k : ℤ, b.val k=positiveScalarExtension (fun n : ℕ+ => ∑' m : ℕ+, ((m:ℕ):ℂ)*u n m) k) ∧
      ‖b‖ ≤ B*(1+3*‖puncturedLattice p hp‖)*‖g‖^2 := by
  obtain ⟨b,hb,hn⟩ := WeightedCoeff.exists_of_weighted_norm_le (Weight.signedSobolev (-1))
    (squaredGapMomentMajorant hp g)
    (positiveScalarExtension (fun n : ℕ+ => ∑' m : ℕ+, ((m:ℕ):ℂ)*u n m)) B hB (by
      intro k
      by_cases hk : k ∈ range positiveEmbedding
      · obtain ⟨n,rfl⟩ := hk
        change ‖(Weight.signedSobolev (-1) ((n:ℕ):ℤ):ℂ)*
          positiveScalarExtension (fun i : ℕ+ => ∑' m : ℕ+, ((m:ℕ):ℂ)*u i m) ((n:ℕ):ℤ)‖ ≤ _
        rw [signed_inverse_weight_positive,positiveScalarExtension_apply]
        exact norm_weighted_positive_moment_row_le hp g u B hB hu n
      · rw [positiveScalarExtension_zero_of_not_mem_range _ k hk,mul_zero,norm_zero]
        positivity)
  refine ⟨b,hb,hn.trans ?_⟩
  calc
    _ ≤ B*((1+3*‖puncturedLattice p hp‖)*‖g‖^2) :=
      mul_le_mul_of_nonneg_left (norm_squaredGapMomentMajorant_le hp g) hB
    _ = _ := by ring

end NLS.Coeff
