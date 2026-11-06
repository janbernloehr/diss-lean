import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-! # A fixed root retains its index in a continuous ordered enumeration

A strictly increasing integer-indexed family cannot move a fixed root
between slots over a connected parameter space. Only continuity of each
coordinate and exhaustive membership of that root are required.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS

theorem continuous_ordered_root_eq_on_connected {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (f : X → ℤ → ℝ)
    (hf : ∀ n : ℤ, Continuous (fun x => f x n))
    (hstrict : ∀ x : X, StrictMono (f x))
    (a : ℝ) (ha : ∀ x : X, ∃ n : ℤ, f x n = a)
    (n : ℤ) (x₀ : X) (h₀ : f x₀ n = a) : ∀ x : X, f x n = a := by
  let S : Set X := {x | f x n = a}
  have hclosed : IsClosed S := isClosed_eq (hf n) continuous_const
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hl : f x (n-1) < a := by
      rw [← hx]
      exact hstrict x (by omega)
    have hu : a < f x (n+1) := by
      rw [← hx]
      exact hstrict x (by omega)
    filter_upwards [(hf (n-1)).continuousAt.eventually (gt_mem_nhds hl),
      (hf (n+1)).continuousAt.eventually (lt_mem_nhds hu)] with y hyl hyu
    obtain ⟨k,hk⟩ := ha y
    have hkn : k = n := by
      rcases lt_trichotomy k n with h | h | h
      · have hb := (hstrict y).monotone (show k ≤ n-1 by omega)
        rw [hk] at hb
        linarith
      · exact h
      · have hb := (hstrict y).monotone (show n+1 ≤ k by omega)
        rw [hk] at hb
        linarith
    change f y n = a
    simpa only [hkn] using hk
  have he : S = univ := (show IsClopen S from ⟨hclosed,hopen⟩).eq_univ ⟨x₀,h₀⟩
  intro x
  have hx : x ∈ S := by rw [he]; trivial
  exact hx

end NLS
