import NLS.SequenceSpaces.DoubledPairL1Majorant
import NLS.SequenceSpaces.SpectralWeight

/-! Positive-index even spectral bounds control both actual signed
weighted tails by the same doubled-pair ell-one envelope. -/
noncomputable section
namespace NLS

theorem even_weighted_tail_envelope (w : SpectralWeight) (f : ℤ → ℂ)
    (hf : ∀ k, f (-k)=f k) (H : Coeff 1) (N : ℕ) (hN : 1 ≤ N) (C : ℝ)
    (hb : ∀ n : ℕ+, N ≤ (n:ℕ) → w (n:ℤ)*‖f (n:ℤ)‖ ≤
      C*‖Coeff.doubledPairMajorant H (n:ℤ)‖) (k : ℤ) (hk : N ≤ k.natAbs) :
    ‖(w k:ℂ)*f k‖ ≤ C*‖Coeff.doubledPairMajorant H k‖ := by
  let n : ℕ+ := ⟨k.natAbs,by omega⟩
  have hn : N ≤ (n:ℕ) := hk
  have hidx : (n:ℤ) = |k| := Int.natCast_natAbs k
  have hfn : f (n:ℤ)=f k := by
    rw [hidx]
    by_cases hp : 0 ≤ k
    · rw [abs_of_nonneg hp]
    · rw [abs_of_neg (by omega),hf]
  have hgn : ‖Coeff.doubledPairMajorant H (n:ℤ)‖ = ‖Coeff.doubledPairMajorant H k‖ :=
    (Coeff.norm_doubledPairMajorant_apply H (n:ℤ)).trans (Coeff.norm_doubledPairMajorant_natAbs H k)
  have h := hb n hn
  rw [hgn,hfn,hidx,SpectralWeight.apply_abs] at h
  simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (w.positive k).le] using h

end NLS
