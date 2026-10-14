import NLS.ComplexAnalysis.ImproperPrimitivePathIntegral
import NLS.ComplexAnalysis.PiecewiseC1Loop

/-!
# Improper integrals along finite piecewise C¹ paths

A continuous finite chain can have corners and singular behavior at its
endpoints. Each piece need only be C¹ in its parameter interior. The
integral is a limit of sums of actual truncated integrals, and primitive
differences telescope across all intermediate vertices.
-/

noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- A finite continuous chain of paths, C¹ on each open piece. Endpoint
derivatives need not exist or match; the empty chain is also allowed. -/
structure PiecewiseInteriorC1Path (a b : ℂ) where
  count : ℕ
  vertex : ℕ → ℂ
  edge : (i : Fin count) → Path (vertex i.val) (vertex (i.val+1))
  smooth : ∀ i, ContDiffOn ℝ 1 (edge i).extend (Ioo 0 1)
  initial : vertex 0 = a
  terminal : vertex count = b

namespace PiecewiseInteriorC1Path
variable {a b : ℂ}

/-- The interiors of all pieces lie in D. -/
def PiecesInside (Γ : PiecewiseInteriorC1Path a b) (D : Set ℂ) : Prop :=
  ∀ i t, t ∈ Ioo (0 : ℝ) 1 → (Γ.edge i).extend t ∈ D

/-- The genuine interior corner vertices also lie in D. -/
def VerticesInside (Γ : PiecewiseInteriorC1Path a b) (D : Set ℂ) : Prop :=
  ∀ k : ℕ, 0 < k → k < Γ.count → Γ.vertex k ∈ D

/-- Sum literal integrals on the truncated pieces. -/
def truncatedIntegral (Γ : PiecewiseInteriorC1Path a b) (f : ℂ → ℂ) (u v : ℝ) : ℂ :=
  ∑ i : Fin Γ.count, truncatedPathIntegral f (Γ.edge i) u v

/-- The improper integral is a limit of the actual truncated sums. -/
def improperIntegral (Γ : PiecewiseInteriorC1Path a b) (f : ℂ → ℂ) : ℂ :=
  limUnder ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ)))
    (fun t : ℝ × ℝ => Γ.truncatedIntegral f t.1 t.2)

/-- Boundary primitive values telescope, including for chains with corners. -/
theorem tendsto_truncatedIntegral_of_primitive_boundary
    (Γ : PiecewiseInteriorC1Path a b) (f F : ℂ → ℂ) (D : Set ℂ)
    (hf : ContinuousOn f D) (hF : ∀ z ∈ D, HasDerivAt F (f z) z)
    (hΓ : Γ.PiecesInside D) (L : ℕ → ℂ)
    (hL : ∀ k ≤ Γ.count, Tendsto F (𝓝[D] (Γ.vertex k)) (𝓝 (L k))) :
    Tendsto (fun t : ℝ × ℝ => Γ.truncatedIntegral f t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ))) (𝓝 (L Γ.count-L 0)) := by
  have hi (i : Fin Γ.count) :
      Tendsto (fun t : ℝ × ℝ => truncatedPathIntegral f (Γ.edge i) t.1 t.2)
        ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ))) (𝓝 (L (i.val+1)-L i.val)) :=
    NLS.ComplexAnalysis.tendsto_truncatedPathIntegral_of_primitive_boundary
      f F D hf hF (Γ.edge i) (Γ.smooth i) (hΓ i)
      (hL i.val i.isLt.le) (hL (i.val+1) i.isLt)
  have he : (∑ i : Fin Γ.count, (L (i.val+1)-L i.val)) = L Γ.count-L 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => L (i+1)-L i) Γ.count]
    exact Finset.sum_range_sub L Γ.count
  simpa only [truncatedIntegral,he] using tendsto_finsetSum Finset.univ (fun i _ => hi i)

/-- The limit-defined piecewise integral equals its boundary difference. -/
theorem improperIntegral_eq_sub
    (Γ : PiecewiseInteriorC1Path a b) (f F : ℂ → ℂ) (D : Set ℂ)
    (hf : ContinuousOn f D) (hF : ∀ z ∈ D, HasDerivAt F (f z) z)
    (hΓ : Γ.PiecesInside D) (L : ℕ → ℂ)
    (hL : ∀ k ≤ Γ.count, Tendsto F (𝓝[D] (Γ.vertex k)) (𝓝 (L k))) :
    Γ.improperIntegral f = L Γ.count-L 0 :=
  (Γ.tendsto_truncatedIntegral_of_primitive_boundary f F D hf hF hΓ L hL).limUnder_eq

/-- If the two boundary limits agree and interior vertices are regular,
all actual truncated piece sums converge to zero. -/
theorem tendsto_truncatedIntegral_eq_zero_of_common_boundary
    (Γ : PiecewiseInteriorC1Path a b) (f F : ℂ → ℂ) (D : Set ℂ)
    (hf : ContinuousOn f D) (hF : ∀ z ∈ D, HasDerivAt F (f z) z)
    (hΓ : Γ.PiecesInside D) (hv : Γ.VerticesInside D) (A : ℂ)
    (ha : Tendsto F (𝓝[D] a) (𝓝 A)) (hb : Tendsto F (𝓝[D] b) (𝓝 A)) :
    Tendsto (fun t : ℝ × ℝ => Γ.truncatedIntegral f t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ))) (𝓝 0) := by
  classical
  let L : ℕ → ℂ := fun k => if k = 0 ∨ k = Γ.count then A else F (Γ.vertex k)
  have hL (k : ℕ) (hk : k ≤ Γ.count) : Tendsto F (𝓝[D] (Γ.vertex k)) (𝓝 (L k)) := by
    by_cases hk0 : k = 0
    · subst k; simpa only [L,Γ.initial,eq_self_iff_true,true_or,ite_true] using ha
    by_cases hkc : k = Γ.count
    · subst k; simpa only [L,Γ.terminal,eq_self_iff_true,or_true,ite_true] using hb
    have hkD := hv k (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hk hkc)
    simp only [L,hk0,hkc,or_self,ite_false]
    exact (hF _ hkD).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [L,eq_self_iff_true,or_true,true_or,ite_true,sub_self] using
    Γ.tendsto_truncatedIntegral_of_primitive_boundary f F D hf hF hΓ L hL

end PiecewiseInteriorC1Path
end NLS.ComplexAnalysis
