import NLS.SequenceSpaces.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Positive-gap pairing of absolutely summable signed weighted moments -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.SequenceSpaces

theorem int_weighted_sum_eq_positive_pairs (F : ℤ → ℂ)
    (hs : Summable (fun k : ℤ => ‖(k : ℂ)*F k‖)) :
    Summable (fun k : ℕ+ => ‖(k : ℂ)*(F (k : ℤ)-F (-(k : ℤ)))‖) ∧
      (∑' k : ℤ, (k : ℂ)*F k)=∑' k : ℕ+, (k : ℂ)*(F (k : ℤ)-F (-(k : ℤ))) := by
  have hi : Function.Injective (fun k : ℕ+ => (k : ℤ)) := by
    intro a b h
    apply Subtype.ext
    exact Int.ofNat.inj h
  have hp : Summable (fun k : ℕ+ => ‖((k : ℤ) : ℂ)*F (k : ℤ)‖) := by
    simpa only [Function.comp_def] using hs.comp_injective hi
  have hn : Summable (fun k : ℕ+ => ‖((-(k : ℤ)) : ℂ)*F (-(k : ℤ))‖) := by
    simpa only [Function.comp_def,Int.cast_neg] using hs.comp_injective (neg_injective.comp hi)
  have he (k : ℕ+) : ((k : ℤ) : ℂ)*F (k : ℤ)+((-(k : ℤ)) : ℂ)*F (-(k : ℤ))=
      (k : ℂ)*(F (k : ℤ)-F (-(k : ℤ))) := by push_cast; ring
  refine ⟨(hp.add hn).of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_),?_⟩
  · rw [←he]
    simpa only [Int.cast_neg] using norm_add_le
      (((k : ℤ) : ℂ)*F (k : ℤ)) (((-(k : ℤ)) : ℂ)*F (-(k : ℤ)))
  · have hsum := tsum_int_eq_zero_add_tsum_pnat hs.of_norm
    simp only [Int.cast_zero,zero_mul,zero_add,Int.cast_neg] at hsum
    exact hsum.trans ((hp.of_norm.tsum_add hn.of_norm).symm.trans (tsum_congr he))

end NLS.SequenceSpaces
