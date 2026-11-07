import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A common open neighborhood bounds a finite family of continuous real functions. -/
open Set Filter Topology
namespace NLS.Topology
variable {X I : Type*} [TopologicalSpace X]

theorem exists_open_finite_continuous_upper_bound (S : Finset I) (f : I → X → ℝ)
    (a : X) (hf : ∀ i ∈ S, ContinuousAt (f i) a) :
    ∃ U : Set X, IsOpen U ∧ a ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ U, ∀ i ∈ S, f i x ≤ C := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨univ,isOpen_univ,mem_univ _,0,le_rfl,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨U,hU,haU,C,hC,hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have he : ∀ᶠ x in 𝓝 a, f i x < f i a+1 :=
      (hf i (Finset.mem_insert_self _ _)) (gt_mem_nhds (lt_add_one _))
    obtain ⟨V,hsub,hV,haV⟩ := mem_nhds_iff.mp he
    refine ⟨U ∩ V,hU.inter hV,⟨haU,haV⟩,max C (f i a+1),hC.trans (le_max_left _ _),?_⟩
    intro x hx j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (hsub hx.2).le.trans (le_max_right _ _)
    · exact (hbound x hx.1 j hj).trans (le_max_left _ _)

end NLS.Topology
