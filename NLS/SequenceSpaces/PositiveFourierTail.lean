import NLS.SequenceSpaces.FourierTail
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Square sums on the two positive-index Fourier tails -/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- Two distinct Fourier coefficients use at most the full Hilbert energy. -/
theorem pair_sq_le_norm_sq (a : Coeff 2) (i j : ℤ) (hij : i ≠ j) :
    ‖a i‖^2+‖a j‖^2 ≤ ‖a‖^2 := by
  have hs : HasSum (fun k : ℤ => ‖a k‖^2) (‖a‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) a
  have h := hs.summable.sum_le_tsum ({i,j} : Finset ℤ) (fun k _ => sq_nonneg ‖a k‖)
  simpa only [Finset.sum_pair hij, hs.tsum_eq] using h

/-- The two signed tails sampled from `N>=1` are disjoint and are bounded
by the exact symmetric Fourier remainder norm. -/
theorem positive_pair_tail_sq (a : Coeff 2) (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun k : ℕ => ‖a (k+N)‖^2+‖a (-(k+N : ℤ))‖^2) ∧
      (∑' k : ℕ, (‖a (k+N)‖^2+‖a (-(k+N : ℤ))‖^2)) ≤ ‖fourierTail N a‖^2 := by
  let f : ℕ ⊕ ℕ → ℤ := Sum.elim (fun k : ℕ => (k : ℤ)+N) (fun k : ℕ => -((k : ℤ)+N))
  have hf : Function.Injective f := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · congr 1
      dsimp [f] at hij
      omega
    · dsimp [f] at hij
      omega
    · dsimp [f] at hij
      omega
    · congr 1
      dsimp [f] at hij
      omega
  have hs : HasSum (fun k : ℤ => ‖fourierTail N a k‖^2) (‖fourierTail N a‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := 2) (by norm_num) (fourierTail N a)
  have hp (k : ℕ) : fourierTail N a ((k : ℤ)+N) = a ((k : ℤ)+N) := by
    rw [fourierTail_apply, if_pos (by omega)]
  have hm (k : ℕ) : fourierTail N a (-((k : ℤ)+N)) = a (-((k : ℤ)+N)) := by
    rw [fourierTail_apply, if_pos (by omega)]
  have hsp : Summable (fun k : ℕ => ‖a ((k : ℤ)+N)‖^2) := by
    simpa only [Function.comp_def, hp] using hs.summable.comp_injective
      (show Function.Injective (fun k : ℕ => (k : ℤ)+N) by intro i j hij; dsimp only at hij; omega)
  have hsm : Summable (fun k : ℕ => ‖a (-((k : ℤ)+N))‖^2) := by
    simpa only [Function.comp_def, hm] using hs.summable.comp_injective
      (show Function.Injective (fun k : ℕ => -((k : ℤ)+N)) by intro i j hij; dsimp only at hij; omega)
  refine ⟨hsp.add hsm, ?_⟩
  have hi := tsum_comp_le_tsum_of_inj hs.summable (fun k => sq_nonneg ‖fourierTail N a k‖) hf
  rw [hs.tsum_eq] at hi
  simp only [Function.comp_def] at hi
  have hl : Summable ((fun k => ‖fourierTail N a (f k)‖^2) ∘ Sum.inl) := by
    simpa only [Function.comp_def, f, Sum.elim_inl, hp] using hsp
  have hr : Summable ((fun k => ‖fourierTail N a (f k)‖^2) ∘ Sum.inr) := by
    simpa only [Function.comp_def, f, Sum.elim_inr, hm] using hsm
  rw [hl.tsum_sum hr] at hi
  simpa only [f, Sum.elim_inl, Sum.elim_inr, hp, hm, ← hsp.tsum_add hsm] using hi

end NLS.Coeff
