import NLS.FunctionalAnalysis.IntegerGridStar
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-! # At most n+1 integer-grid stars meet at any point

On the chain of vertices meeting at x, the sum of coordinate increments
above floor(x) is an injective integer rank between zero and n.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.FunctionalAnalysis
universe u v
variable {ι : Type u} [Fintype ι]

/-- Integer rank relative to the coordinatewise floor of x. -/
def integerGridVertexRank (x : ι → ℝ) (v : ι → ℤ) : ℤ :=
  ∑ i, (v i - ⌊x i⌋)

theorem integerGridVertexRank_bounds {x : ι → ℝ} {v : ι → ℤ}
    (hv : x ∈ integerGridStar v) :
    0 ≤ integerGridVertexRank x v ∧ integerGridVertexRank x v ≤ (Fintype.card ι : ℤ) := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (integerGridStar_vertex_bounds hv i).1)
  · have h := Finset.sum_le_sum (s := Finset.univ) (f := fun i => v i - ⌊x i⌋)
      (g := fun _ => (1 : ℤ)) (fun i _ => by have := (integerGridStar_vertex_bounds hv i).2; omega)
    simpa only [integerGridVertexRank,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using h

/-- Rank separates all integer vertices whose stars contain the fixed point. -/
theorem integerGridVertexRank_injOn (x : ι → ℝ) :
    Set.InjOn (integerGridVertexRank x) {v | x ∈ integerGridStar v} := by
  have H (a b : ι → ℤ) (hle : a ≤ b)
      (he : integerGridVertexRank x a = integerGridVertexRank x b) : a = b := by
    funext i
    apply le_antisymm (hle i)
    by_contra hn
    have hi : a i < b i := lt_of_not_ge hn
    have hs := Finset.sum_lt_sum (s := Finset.univ)
      (f := fun j => a j - ⌊x j⌋) (g := fun j => b j - ⌊x j⌋)
      (fun j _ => sub_le_sub_right (hle j) _) ⟨i,Finset.mem_univ _,sub_lt_sub_right hi _⟩
    exact (ne_of_lt hs) he
  intro a ha b hb he
  rcases integerGridStar_vertices_comparable ha hb with h | h
  · exact H a b h he
  · exact (H b a h he.symm).symm

/-- Any family of distinct grid stars containing one point has size at most n+1. -/
theorem card_le_of_mem_integerGridStar {κ : Type v} [Fintype κ] (x : ι → ℝ)
    (f : κ → (ι → ℤ)) (hf : Function.Injective f) (hmem : ∀ k, x ∈ integerGridStar (f k)) :
    Fintype.card κ ≤ Fintype.card ι + 1 := by
  let g : κ → Fin (Fintype.card ι + 1) := fun k =>
    ⟨(integerGridVertexRank x (f k)).toNat,by
      have := integerGridVertexRank_bounds (hmem k)
      omega⟩
  have hg : Function.Injective g := by
    intro a b he
    apply hf
    apply integerGridVertexRank_injOn x (hmem a) (hmem b)
    have h := congrArg Fin.val he
    change (integerGridVertexRank x (f a)).toNat = (integerGridVertexRank x (f b)).toNat at h
    have ha := (integerGridVertexRank_bounds (hmem a)).1
    have hb := (integerGridVertexRank_bounds (hmem b)).1
    omega
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective g hg

end NLS.FunctionalAnalysis
