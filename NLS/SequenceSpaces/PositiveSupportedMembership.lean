import NLS.SequenceSpaces.Basic

/-! # Hilbert membership from square summability on the strictly positive integers -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS

theorem memlp_two_of_positive_support (f : ℤ → ℂ)
    (hz : ∀ k : ℤ, k ≤ 0 → f k=0)
    (hs : Summable (fun n : ℕ+ => ‖f (n : ℤ)‖^2)) : Memℓp f 2 := by
  have hi : Function.Injective (fun n : ℕ+ => (n : ℤ)) := by
    intro n m h
    apply Subtype.ext
    exact Int.ofNat.inj h
  have hzero (k : ℤ) (hk : k ∉ range (fun n : ℕ+ => (n : ℤ))) : ‖f k‖^2=0 := by
    have hn : k ≤ 0 := by
      by_contra h
      have hp : 0 < k := by omega
      apply hk
      exact ⟨⟨k.toNat,by omega⟩,by change (k.toNat : ℤ)=k;omega⟩
    simp only [hz k hn,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0)]
  have hfull : Summable (fun k : ℤ => ‖f k‖^2) := (hi.summable_iff hzero).mp hs
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hfull

end NLS
