import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finitely many local monotone majorant predicates share an open
neighborhood and one nonnegative bound. -/
noncomputable section
open Set
open scoped Classical
namespace NLS.ComplexAnalysis

theorem exists_common_open_finite_majorant {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (x : X) (P : ι → X → ℝ → Prop)
    (hmono : ∀ i y C D, C ≤ D → P i y C → P i y D)
    (hlocal : ∀ i ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, P i y C) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ i ∈ s, ∀ y ∈ U, P i y C := by
  choose U hU hx C hC hP using fun i : s => hlocal i i.property
  refine ⟨⋂ i : s, U i,isOpen_iInter_of_finite hU,mem_iInter.mpr hx,
    ∑ i : s, C i,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro i hi y hy
  exact hmono i y _ _ (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ ⟨i,hi⟩))
    (hP ⟨i,hi⟩ y (mem_iInter.mp hy ⟨i,hi⟩))

end NLS.ComplexAnalysis
