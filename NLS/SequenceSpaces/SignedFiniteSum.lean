import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Even finite sums over symmetric signed indices -/
noncomputable section
open scoped BigOperators
namespace NLS

theorem sum_symmetric_int_eq_twice_positive
    (s : Finset ℤ) (hz : (0 : ℤ) ∉ s)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) (f : ℤ → ℝ)
    (hf : ∀ n : ℤ, f (-n) = f n) :
    ∑ n ∈ s, f n = 2*∑ n ∈ s.filter (fun n => 0 < n), f n := by
  classical
  let t := s.filter (fun n => 0 < n)
  have he : s = t ∪ t.image Neg.neg := by
    ext n
    simp only [Finset.mem_union,Finset.mem_image,t,Finset.mem_filter]
    constructor
    · intro hn
      rcases lt_trichotomy n 0 with h | h | h
      · exact Or.inr ⟨-n,⟨(hs n).mpr hn,by omega⟩,neg_neg n⟩
      · exact False.elim (hz (h ▸ hn))
      · exact Or.inl ⟨hn,h⟩
    · rintro (⟨hn,_⟩ | ⟨m,⟨hm,_⟩,rfl⟩)
      · exact hn
      · exact (hs m).mpr hm
  have hd : Disjoint t (t.image Neg.neg) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    obtain ⟨m,hm,hmn⟩ := Finset.mem_image.mp hn'
    have hnp := (Finset.mem_filter.mp hn).2
    have hmp := (Finset.mem_filter.mp hm).2
    omega
  change (∑ n ∈ s, f n) = 2*∑ n ∈ t, f n
  rw [he,Finset.sum_union hd,Finset.sum_image (by
    intro a _ b _ hab
    exact neg_injective hab)]
  simp only [hf]
  rw [two_mul]

end NLS
