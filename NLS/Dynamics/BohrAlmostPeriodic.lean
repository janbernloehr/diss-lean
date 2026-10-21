import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform almost periodicity from compact isometric orbits

Bohr almost periodicity requires relatively dense uniform epsilon-periods.
A finite orbit net supplies these periods; continuous maps on compact sets
preserve the property.
-/

noncomputable section
open Set Metric
namespace NLS.Dynamics

/-- Bohr almost periodicity: continuity and relatively dense uniform
epsilon-periods, in the metric of the actual target space. -/
structure BohrAlmostPeriodic {X : Type*} [PseudoMetricSpace X] (f : ℝ → X) : Prop where
  continuous : Continuous f
  periods : ∀ ε > 0, ∃ L > 0, ∀ a : ℝ, ∃ τ ∈ Icc a (a+L),
    ∀ t : ℝ, dist (f (t+τ)) (f t) < ε

/-- A continuous orbit with compact metric behavior and translation-invariant
distances has relatively dense uniform return times. -/
theorem bohrAlmostPeriodic_of_totallyBounded_range
    {X : Type*} [PseudoMetricSpace X] (f : ℝ → X) (hf : Continuous f)
    (hcompact : TotallyBounded (range f))
    (hshift : ∀ t u v : ℝ, dist (f (t+u)) (f (t+v)) = dist (f u) (f v)) :
    BohrAlmostPeriodic f := by
  classical
  refine ⟨hf, ?_⟩
  intro ε hε
  obtain ⟨T,hT,hfinite,hcover⟩ := Metric.finite_approx_of_totallyBounded hcompact ε hε
  let : Fintype T := hfinite.fintype
  let g : T → ℝ := fun y => Classical.choose (hT y.property)
  have hg (y : T) : f (g y) = y.val := Classical.choose_spec (hT y.property)
  let R : ℝ := 1 + ∑ y : T, |g y|
  have hRpos : 0 < R := by
    have hs : 0 ≤ ∑ y : T, |g y| := Finset.sum_nonneg (fun y _ => abs_nonneg (g y))
    dsimp only [R]
    linarith
  have hR (y : T) : |g y| ≤ R := by
    have h := Finset.single_le_sum (fun z (_ : z ∈ (Finset.univ : Finset T)) => abs_nonneg (g z))
      (Finset.mem_univ y)
    dsimp only [R]
    linarith
  refine ⟨2*R, by positivity, ?_⟩
  intro a
  have hc := hcover (mem_range_self (a+R))
  simp only [mem_iUnion, mem_ball] at hc
  obtain ⟨y,hy,hnear⟩ := hc
  let s := g ⟨y,hy⟩
  have hs : -R ≤ s ∧ s ≤ R := abs_le.mp (hR ⟨y,hy⟩)
  have hnear' : dist (f (a+R)) (f s) < ε := by
    rw [hg]
    exact hnear
  refine ⟨a+R-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
  intro t
  have heq := hshift (t-s) (a+R) s
  have h₁ : (t-s)+(a+R) = t+(a+R-s) := by ring
  have h₂ : (t-s)+s = t := by ring
  rw [h₁,h₂] at heq
  exact heq.trans_lt hnear'

/-- A continuous change of coordinates on a compact set preserves uniform
almost periodicity, without any global uniform-continuity assumption. -/
theorem BohrAlmostPeriodic.comp_continuousOn_compact
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} (hf : BohrAlmostPeriodic f) (K : Set X) (hK : IsCompact K)
    (hmem : ∀ t, f t ∈ K) (g : X → Y) (hg : ContinuousOn g K) :
    BohrAlmostPeriodic (g ∘ f) := by
  refine ⟨hg.comp_continuous hf.continuous hmem, ?_⟩
  intro ε hε
  obtain ⟨δ,hδ,hsmall⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hg) ε hε
  obtain ⟨L,hL,hperiods⟩ := hf.periods δ hδ
  refine ⟨L,hL,?_⟩
  intro a
  obtain ⟨τ,hτ,hreturn⟩ := hperiods a
  exact ⟨τ,hτ,fun t => hsmall _ (hmem (t+τ)) _ (hmem t) (hreturn t)⟩

end NLS.Dynamics
