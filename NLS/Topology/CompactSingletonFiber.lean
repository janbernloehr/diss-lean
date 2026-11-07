import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-! Compactness gives inverse continuity at a singleton fiber without
requiring injectivity at any other fiber. All filter statements allow an
eventual compact-set restriction rather than a bound on the whole net. -/
noncomputable section
open Set Filter Topology
namespace NLS.Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- Every neighborhood of the unique fiber point contains the full inverse
image of some target neighborhood, after restriction to the compact set. -/
theorem exists_nhds_of_compact_singleton_fiber (K : Set X) (hK : IsCompact K)
    (f : X → Y) (hf : ContinuousOn f K) (a : X)
    (hu : ∀ x ∈ K, f x=f a → x=a) (U : Set X) (hU : U ∈ 𝓝 a) :
    ∃ V ∈ 𝓝 (f a), ∀ x ∈ K, f x ∈ V → x ∈ U := by
  obtain ⟨W,hWU,hW,haW⟩ := mem_nhds_iff.mp hU
  have hc : IsCompact (K ∩ Wᶜ) := hK.inter_right hW.isClosed_compl
  have hi : IsClosed (f '' (K ∩ Wᶜ)) := (hc.image_of_continuousOn (hf.mono inter_subset_left)).isClosed
  have ha : f a ∈ (f '' (K ∩ Wᶜ))ᶜ := by
    rintro ⟨x,⟨hx,hxW⟩,hxa⟩
    exact hxW ((hu x hx hxa) ▸ haW)
  refine ⟨_,hi.isOpen_compl.mem_nhds ha,fun x hx hfx => ?_⟩
  apply hWU
  by_contra hxW
  exact hfx ⟨x,⟨hx,hxW⟩,rfl⟩

/-- An eventually compact net converges to the singleton fiber point as soon
as its images converge there. No injectivity elsewhere is assumed. -/
theorem tendsto_of_compact_singleton_fiber (K : Set X) (hK : IsCompact K)
    (f : X → Y) (hf : ContinuousOn f K) (a : X)
    (hu : ∀ x ∈ K, f x=f a → x=a) {Z : Type*} {l : Filter Z}
    (x : Z → X) (hbound : ∀ᶠ k in l, x k ∈ K)
    (hout : Tendsto (f ∘ x) l (𝓝 (f a))) : Tendsto x l (𝓝 a) := by
  apply tendsto_def.mpr
  intro U hU
  obtain ⟨V,hV,hVU⟩ := exists_nhds_of_compact_singleton_fiber K hK f hf a hu U hU
  filter_upwards [hbound,hout hV] with k hk hfk
  exact hVU (x k) hk hfk

/-- Finitely many continuous metric-valued tests control a continuous
observable near a singleton fiber, uniformly over a compact source space. -/
theorem exists_finite_coordinate_control_at_singleton
    {A ι Z E : Type*} [TopologicalSpace A] [CompactSpace A]
    [MetricSpace Z] [PseudoMetricSpace E]
    (c : A → ι → Z) (hc : ∀ i, Continuous (fun x => c x i))
    (a : A) (hu : ∀ x, c x=c a → x=a) (f : A → E) (hf : Continuous f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset ι, ∃ δ > 0, ∀ x : A,
      (∀ i ∈ J, dist (c x i) (c a i) < δ) → dist (f x) (f a) < ε := by
  classical
  let I := ι × {δ : ℝ // 0 < δ}
  let U : I → Set A := fun i => {x | i.2.val < dist (c x i.1) (c a i.1)}
  let K : Set A := {x | ε ≤ dist (f x) (f a)}
  have hK : IsCompact K := (isClosed_le continuous_const (hf.dist continuous_const)).isCompact
  have hU : ∀ i, IsOpen (U i) := fun i =>
    isOpen_lt continuous_const ((hc i.1).dist continuous_const)
  have hcover : K ⊆ ⋃ i, U i := by
    intro x hx
    have hne : x ≠ a := by
      rintro rfl
      exact (not_le_of_gt hε) (by simpa only [K,mem_ofPred_eq,dist_self] using hx)
    have hnc : ∃ i, c x i ≠ c a i := by
      by_contra! h
      exact hne (hu x (funext h))
    obtain ⟨i,hi⟩ := hnc
    have hd : 0 < dist (c x i) (c a i) := dist_pos.mpr hi
    exact mem_iUnion.mpr ⟨(i,⟨dist (c x i) (c a i)/2,by positivity⟩),by
      change dist (c x i) (c a i)/2 < dist (c x i) (c a i)
      linarith⟩
  obtain ⟨J,hJ⟩ := hK.elim_finite_subcover U hU hcover
  have htol : ∀ S : Finset I, ∃ δ > 0, ∀ i ∈ S, δ ≤ i.2.val := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert i S _ ih =>
      obtain ⟨δ,hδ,hs⟩ := ih
      refine ⟨min i.2.val δ,lt_min i.2.property hδ,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hs j hj)
  obtain ⟨δ,hδ,ht⟩ := htol J
  refine ⟨J.image Prod.fst,δ,hδ,fun x hx => ?_⟩
  by_contra! hn
  obtain ⟨i,hiJ,hiU⟩ := mem_iUnion₂.mp (hJ (show x ∈ K from hn))
  exact (not_lt_of_ge (ht i hiJ))
    (hiU.trans (hx i.1 (Finset.mem_image.mpr ⟨i,hiJ,rfl⟩)))

end NLS.Topology
