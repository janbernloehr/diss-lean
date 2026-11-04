import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- Finitely many continuous nonzero complex functions have a common
positive norm lower bound on one ball around the base point. -/
theorem exists_finite_family_norm_lower_bound
    {ι X : Type*} [Finite ι] [PseudoMetricSpace X]
    (F : ι → X → ℂ) (x0 : X) (hF : ∀ i, ContinuousAt (F i) x0)
    (hne : ∀ i, F i x0≠0) :
    ∃ δ c : ℝ, 0<δ ∧ 0<c ∧ ∀ x∈ball x0 δ, ∀ i, c≤‖F i x‖ := by
  let K := range (fun i : ι => ‖F i x0‖)
  have hK : IsCompact K := (Set.finite_range _).isCompact
  obtain ⟨c,hc,hbase⟩ := hK.exists_forall_le' continuousOn_id (by
    intro y hy
    obtain ⟨i,rfl⟩ := hy
    exact norm_pos_iff.mpr (hne i))
  have hex (i : ι) : ∃ r : ℝ, 0<r ∧ ball x0 r⊆{x | c/2<‖F i x‖} := by
    have hi : c/2<‖F i x0‖ := by have hh : c≤‖F i x0‖ := hbase _ ⟨i,rfl⟩;linarith
    exact Metric.mem_nhds_iff.mp ((hF i).norm (lt_mem_nhds hi))
  choose r hr hball using hex
  let U : Set X := ⋂ i : ι, ball x0 (r i)
  have hU : IsOpen U := isOpen_iInter_of_finite (fun _ => isOpen_ball)
  have hx0 : x0∈U := mem_iInter.mpr (fun i => mem_ball_self (hr i))
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx0)
  refine ⟨δ,c/2,hδ,by positivity,?_⟩
  intro x hx i
  exact (hball i (mem_iInter.mp (hδball hx) i)).le

end NLS.ComplexAnalysis
