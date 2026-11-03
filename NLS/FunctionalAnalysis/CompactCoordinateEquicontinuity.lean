import NLS.FunctionalAnalysis.CompactCoordinateControl
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Equicontinuity detected by compact separating coordinates

On a compact target, equicontinuity of each separating coordinate controls
every continuous metric-valued observable. Together with Arzelà–Ascoli this
gives uniform subsequences, without a common modulus across all coordinates.
-/
noncomputable section
open Set Filter Topology
open scoped BoundedContinuousFunction
namespace NLS

/-- Equicontinuity of every separating coordinate implies equicontinuity of
any continuous metric-valued observable of a compact target. -/
theorem equicontinuousAt_observable_of_coordinates
    {X ι Z Y A T : Type*} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Z] [PseudoMetricSpace Y] [TopologicalSpace T]
    (c : X → ι → Z) (hc : ∀ i, Continuous (fun x => c x i))
    (hi : Function.Injective c) (f : X → Y) (hf : Continuous f)
    (F : A → T → X) (t : T)
    (h : ∀ i, EquicontinuousAt (fun a s => c (F a s) i) t) :
    EquicontinuousAt (fun a s => f (F a s)) t := by
  apply Metric.equicontinuousAt_iff_right.mpr
  intro ε hε
  obtain ⟨J, δ, hδ, hJ⟩ :=
    exists_finite_coordinates_control_on_compact c hc hi f hf ε hε
  have he : ∀ᶠ s in 𝓝 t, ∀ i ∈ J, ∀ a,
      dist (c (F a t) i) (c (F a s) i) < δ :=
    (eventually_all_finset J).mpr fun i _ =>
      (Metric.equicontinuousAt_iff_right.mp (h i)) δ hδ
  exact he.mono fun s hs a => hJ (F a t) (F a s) (fun i hiJ => hs i hiJ a)

/-- The coordinate criterion for equicontinuity holds on arbitrary domains. -/
theorem equicontinuous_observable_of_coordinates
    {X ι Z Y A T : Type*} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Z] [PseudoMetricSpace Y] [TopologicalSpace T]
    (c : X → ι → Z) (hc : ∀ i, Continuous (fun x => c x i))
    (hi : Function.Injective c) (f : X → Y) (hf : Continuous f)
    (F : A → T → X)
    (h : ∀ i, Equicontinuous (fun a s => c (F a s) i)) :
    Equicontinuous (fun a s => f (F a s)) :=
  fun t => equicontinuousAt_observable_of_coordinates c hc hi f hf F t (fun i => h i t)

/-- Equicontinuous sequences in a compact metric target range have a uniformly
convergent subsequence on any compact topological domain. -/
theorem exists_subseq_tendstoUniformly_of_equicontinuous_compact_range
    {T Y : Type*} [TopologicalSpace T] [CompactSpace T] [MetricSpace Y]
    (F : ℕ → T → Y) (K : Set Y) (hK : IsCompact K)
    (hF : ∀ n t, F n t ∈ K) (he : Equicontinuous F) :
    ∃ g : C(T,Y), (∀ t, g t ∈ K) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun n t => F (φ n) t) g atTop := by
  let B : ℕ → T →ᵇ Y := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨F n, he.continuous n⟩
  have hB : Equicontinuous ((↑) : range B → T → Y) := by
    choose k hk using fun b : range B => b.property
    have h := he.comp k
    change Equicontinuous (fun b : range B => fun s => B (k b) s) at h
    simpa only [hk] using h
  have hc := BoundedContinuousFunction.arzela_ascoli K hK (range B)
    (by rintro _ t ⟨n, rfl⟩; exact hF n t) hB
  obtain ⟨g, hg, φ, hφ, ht⟩ := hc.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ht
  refine ⟨g.toContinuousMap, ?_, φ, hφ, hu⟩
  intro t
  exact hK.isClosed.mem_of_tendsto (hu.tendsto_at t)
    (Eventually.of_forall fun n => hF (φ n) t)

end NLS
