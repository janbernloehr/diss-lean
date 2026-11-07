import NLS.SequenceSpaces.CoefficientRestriction
import NLS.SequenceSpaces.SandwichMajorant

/-! The two sampled resonant tails form one positive signed ell-one
majorant with norm at most twice the original envelope norm. -/
noncomputable section
namespace NLS.Coeff

private def doubleEmbedding : ℤ ↪ ℤ := ⟨fun k => 2*k,by intro a b h; dsimp at h; omega⟩
private def negativeDoubleEmbedding : ℤ ↪ ℤ := ⟨fun k => -(2*k),by intro a b h; dsimp at h; omega⟩

def doubledPairMajorant (H : Coeff 1) : Coeff 1 :=
  magnitude (restrictIndices doubleEmbedding H)+magnitude (restrictIndices negativeDoubleEmbedding H)

theorem norm_doubledPairMajorant_le (H : Coeff 1) : ‖doubledPairMajorant H‖ ≤ 2*‖H‖ := by
  have hh := norm_add_le (magnitude (restrictIndices doubleEmbedding H))
    (magnitude (restrictIndices negativeDoubleEmbedding H))
  rw [norm_magnitude, norm_magnitude] at hh
  exact hh.trans (by linarith [norm_restrictIndices_le doubleEmbedding H,
    norm_restrictIndices_le negativeDoubleEmbedding H])

theorem norm_doubledPairMajorant_apply (H : Coeff 1) (k : ℤ) :
    ‖doubledPairMajorant H k‖ = ‖H (2*k)‖+‖H (-(2*k))‖ := by
  change ‖(‖H (2*k)‖:ℂ)+(‖H (-(2*k))‖:ℂ)‖ = _
  rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem norm_doubledPairMajorant_natAbs (H : Coeff 1) (k : ℤ) :
    ‖H (2*(k.natAbs:ℤ))‖+‖H (-(2*(k.natAbs:ℤ)))‖ = ‖doubledPairMajorant H k‖ := by
  rw [norm_doubledPairMajorant_apply, Int.natCast_natAbs]
  by_cases hk : 0 ≤ k
  · rw [abs_of_nonneg hk]
  · rw [abs_of_neg (by omega), mul_neg, neg_neg, add_comm]

end NLS.Coeff
