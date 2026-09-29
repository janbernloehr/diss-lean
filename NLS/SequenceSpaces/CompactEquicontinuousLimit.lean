import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Compactness.Compact

/-!
# Uniform limits from eventual local Lipschitz estimates

On a compact metric parameter space, pointwise convergence to a
continuous limit is uniform when one local Lipschitz estimate holds
eventually in the index at every parameter. Exceptional indices and
the local radii may depend on the parameter.
-/

noncomputable section
open Set Filter Topology Metric
namespace NLS

theorem tendstoUniformly_of_eventual_local_lipschitz
    {X Y ι : Type*} [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    (l : Filter ι) (F : ι → X → Y) (f : X → Y)
    (hf : Continuous f) (hpoint : ∀ x : X, Tendsto (fun i => F i x) l (𝓝 (f x)))
    (hlocal : ∀ x : X, ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ᶠ i in l, ∀ y ∈ ball x r, dist (F i y) (F i x) ≤ L*dist y x) :
    TendstoUniformly F f l := by
  apply tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  obtain ⟨r,L,hr,hL,hLip⟩ := hlocal x
  have hthird : 0 < ε/3 := by positivity
  obtain ⟨s,hs,hfball⟩ := Metric.mem_nhds_iff.mp
    (hf.continuousAt (ball_mem_nhds (f x) hthird))
  let δ := min r (min s (ε/(3*(L+1))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ ≤ r := min_le_left _ _
  have hδs : δ ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε/(3*(L+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hcenter : ∀ᶠ i in l, dist (F i x) (f x) < ε/3 := by
    simpa only [mem_ball] using (hpoint x).eventually (ball_mem_nhds (f x) hthird)
  refine ⟨ball x δ,ball_mem_nhds x hδ,?_⟩
  filter_upwards [hLip,hcenter] with i hi hc
  intro y hy
  have hyr : y ∈ ball x r := (ball_subset_ball hδr) hy
  have hys : y ∈ ball x s := (ball_subset_ball hδs) hy
  have hfy : dist (f y) (f x) < ε/3 := mem_ball.mp (hfball hys)
  have hvar : dist (F i y) (F i x) ≤ ε/3 := by
    apply (hi y hyr).trans
    calc
      L*dist y x ≤ (L+1)*dist y x := by nlinarith [dist_nonneg (x := y) (y := x)]
      _ ≤ (L+1)*(ε/(3*(L+1))) :=
        mul_le_mul_of_nonneg_left ((le_of_lt (mem_ball.mp hy)).trans hδε) (by positivity)
      _ = ε/3 := by
        have hne : L+1 ≠ 0 := by positivity
        field_simp [hne]
  have htri : dist (f y) (F i y) ≤
      dist (f y) (f x) + dist (f x) (F i x) + dist (F i x) (F i y) := by
    calc
      dist (f y) (F i y) ≤ dist (f y) (f x) + dist (f x) (F i y) := dist_triangle _ _ _
      _ ≤ dist (f y) (f x) + (dist (f x) (F i x) + dist (F i x) (F i y)) :=
        add_le_add le_rfl (dist_triangle _ _ _)
      _ = _ := by ring
  rw [dist_comm (f x) (F i x),dist_comm (F i x) (F i y)] at htri
  linarith

end NLS
