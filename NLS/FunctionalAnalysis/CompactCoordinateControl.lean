import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Finite coordinate control on compact spaces

A continuous family of separating metric-valued coordinates controls every
continuous metric-valued observable, uniformly on a compact space. The
finite coordinates and their common tolerance are chosen before the points.
-/
noncomputable section
open Set Filter Topology
namespace NLS

/-- On a compact space, finitely many separating coordinate tests control
any continuous observable, with one positive tolerance for all points. -/
theorem exists_finite_coordinates_control_on_compact
    {X ι Z Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Z] [PseudoMetricSpace Y]
    (c : X → ι → Z) (hc : ∀ i, Continuous (fun x => c x i))
    (hi : Function.Injective c) (f : X → Y) (hf : Continuous f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset ι, ∃ δ > 0, ∀ a b : X,
      (∀ i ∈ J, dist (c a i) (c b i) < δ) → dist (f a) (f b) < ε := by
  classical
  let I := ι × {δ : ℝ // 0 < δ}
  let U : I → Set (X × X) := fun i =>
    {v | i.2.val < dist (c v.1 i.1) (c v.2 i.1)}
  let K : Set (X × X) := {v | ε ≤ dist (f v.1) (f v.2)}
  have hK : IsCompact K :=
    (isClosed_le continuous_const
      ((hf.comp continuous_fst).dist (hf.comp continuous_snd))).isCompact
  have hU : ∀ i, IsOpen (U i) := fun i =>
    isOpen_lt continuous_const
      (((hc i.1).comp continuous_fst).dist ((hc i.1).comp continuous_snd))
  have hcover : K ⊆ ⋃ i, U i := by
    intro v hv
    have hne : v.1 ≠ v.2 := by
      intro he
      have : ε ≤ 0 := by simpa only [K, mem_ofPred_eq, he, dist_self] using hv
      exact (not_le_of_gt hε) this
    have hnc : ∃ i, c v.1 i ≠ c v.2 i := by
      by_contra! h
      exact hne (hi (funext h))
    obtain ⟨i, hi'⟩ := hnc
    have hd : 0 < dist (c v.1 i) (c v.2 i) := dist_pos.mpr hi'
    exact mem_iUnion.mpr ⟨(i, ⟨dist (c v.1 i) (c v.2 i) / 2, by positivity⟩),
      (show dist (c v.1 i) (c v.2 i) / 2 < dist (c v.1 i) (c v.2 i) by linarith)⟩
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover U hU hcover
  have htol : ∀ S : Finset I, ∃ δ > 0, ∀ i ∈ S, δ ≤ i.2.val := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i S _ ih =>
      obtain ⟨δ, hδ, hs⟩ := ih
      refine ⟨min i.2.val δ, lt_min i.2.property hδ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hs j hj)
  obtain ⟨δ, hδ, ht⟩ := htol J
  refine ⟨J.image Prod.fst, δ, hδ, fun a b hab => ?_⟩
  by_contra! hn
  obtain ⟨i, hiJ, hiU⟩ := mem_iUnion₂.mp (hJ (show (a, b) ∈ K from hn))
  exact (not_lt_of_ge (ht i hiJ))
    (hiU.trans (hab i.1 (Finset.mem_image.mpr ⟨i, hiJ, rfl⟩)))

/-- Uniform convergence of every separating coordinate on a compact target
implies uniform convergence of every continuous metric-valued observable.
The parameter set and convergence filter are arbitrary. -/
theorem tendstoUniformly_observable_of_coordinates
    {X ι Z Y A B : Type*} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Z] [PseudoMetricSpace Y]
    (c : X → ι → Z) (hc : ∀ i, Continuous (fun x => c x i))
    (hi : Function.Injective c) (f : X → Y) (hf : Continuous f)
    (F : A → B → X) (g : B → X) (l : Filter A)
    (h : ∀ i, TendstoUniformly (fun a b => c (F a b) i) (fun b => c (g b) i) l) :
    TendstoUniformly (fun a b => f (F a b)) (fun b => f (g b)) l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨J, δ, hδ, hJ⟩ :=
    exists_finite_coordinates_control_on_compact c hc hi f hf ε hε
  have he : ∀ᶠ a in l, ∀ i ∈ J, ∀ b, dist (c (g b) i) (c (F a b) i) < δ :=
    (eventually_all_finset J).mpr fun i _ => (Metric.tendstoUniformly_iff.mp (h i)) δ hδ
  exact he.mono fun a ha b => hJ (g b) (F a b) (fun i hiJ => ha i hiJ b)

end NLS
