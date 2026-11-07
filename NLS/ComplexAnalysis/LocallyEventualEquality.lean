import Mathlib.Topology.Connected.Clopen
import Mathlib.Order.Filter.Basic

/-! Eventual equality propagates through an ENTIRE connected parameter
space from local overlap witnesses; no global cutoff is postulated. -/
noncomputable section
open Set Filter Topology
namespace NLS

theorem eventuallyEq_of_locally_eventuallyEq
    {X ι Y : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (l : Filter ι) (f : X → ι → Y)
    (hf : ∀ x,∃ U : Set X,IsOpen U ∧ x∈U ∧ ∀ y∈U,f y=ᶠ[l]f x)
    (x y : X) : f y=ᶠ[l]f x := by
  let S := {z | f z=ᶠ[l]f x}
  have hs : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U,hU,hzU,hu⟩ := hf z
    exact ⟨U,(fun t ht => (hu t ht).trans hz),hU,hzU⟩
  have hc : IsOpen Sᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U,hU,hzU,hu⟩ := hf z
    refine ⟨U,?_,hU,hzU⟩
    intro t ht htx
    exact hz ((hu t ht).symm.trans htx)
  have he : S=univ := (show IsClopen S from ⟨by simpa only [compl_compl] using hc.isClosed_compl,hs⟩).eq_univ ⟨x,EventuallyEq.rfl⟩
  have hy : y∈S := by rw [he];trivial
  exact hy

end NLS
