import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Set.Finite.Basic

/-! # Finite original signed support bounds all positive physical slots -/
noncomputable section
set_option autoImplicit false
namespace NLS

theorem exists_finite_positive_support_of_finite_signed_support (a : ℤ → ℂ)
    (hf : (Function.support a).Finite) :
    ∃ S : Finset ℕ+, ∀ n : ℕ+, n∉S → a (n : ℤ)=0 := by
  classical
  have hi : Function.Injective (fun n : ℕ+ => (n : ℤ)) := by
    intro n m h
    apply Subtype.ext
    exact Int.ofNat.inj h
  have hp : {n : ℕ+ | a (n : ℤ)≠0}.Finite :=
    hf.preimage (fun _ _ _ _ h => hi h)
  refine ⟨hp.toFinset,?_⟩
  intro n hn
  by_contra h
  exact hn (hp.mem_toFinset.mpr h)

end NLS
