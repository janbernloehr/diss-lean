import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! A sphere contained in an open set has a closed outward annular collar. -/
open Set Metric
namespace NLS

/-- A zero-free or resolvent circle in an open set can be enlarged slightly
without crossing its closed complement. No condition on the disk interior is needed. -/
theorem exists_closedAnnulus_subset_of_sphere_subset_open
    {X : Type*} [MetricSpace X] [ProperSpace X]
    (c : X) (r : ℝ) {U : Set X} (hU : IsOpen U) (hs : sphere c r ⊆ U) :
    ∃ R : ℝ, r < R ∧ closedBall c R \ ball c r ⊆ U := by
  let K := closedBall c (r+1) ∩ (Uᶜ ∩ {z | r ≤ dist z c})
  have hK : IsCompact K := (isCompact_closedBall c (r+1)).inter_right
    (hU.isClosed_compl.inter (isClosed_le continuous_const (continuous_id.dist continuous_const)))
  by_cases hn : K.Nonempty
  · obtain ⟨w,hw,hmin⟩ := hK.exists_isMinOn (f := fun z => dist z c) hn (continuous_id.dist continuous_const).continuousOn
    have hwr : r < dist w c := by
      apply lt_of_le_of_ne hw.2.2
      intro he
      exact hw.2.1 (hs (mem_sphere.mpr he.symm))
    let R := min (r+1) ((r+dist w c)/2)
    have hR : r < R := lt_min (by linarith) (by linarith)
    refine ⟨R,hR,?_⟩
    intro z hz
    by_contra hnot
    have hzK : z ∈ K := ⟨(mem_closedBall.mp hz.1).trans (min_le_left _ _),hnot,
      (show r ≤ dist z c from not_lt.mp hz.2)⟩
    have hm : dist w c ≤ dist z c := hmin hzK
    have hupper := (mem_closedBall.mp hz.1).trans (min_le_right _ _)
    linarith
  · refine ⟨r+1,by linarith,?_⟩
    intro z hz
    by_contra hnot
    exact hn ⟨z,hz.1,hnot,(show r ≤ dist z c from not_lt.mp hz.2)⟩

end NLS
