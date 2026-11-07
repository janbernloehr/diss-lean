import NLS.FunctionalAnalysis.IntegralCurveJoin
import NLS.FunctionalAnalysis.IntegralCurveUniqueness
import Mathlib.Analysis.Calculus.MeanValue

/-! Finite endpoint continuation for a C1 Banach vector field with
compact conserved fibers. Compactness bounds the actual speed and
keeps the endpoint limit in the same fiber. No norm conservation is used. -/
noncomputable section
open Set Metric Filter Topology
open scoped NNReal
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {S : Type*}

structure CompactInvariantVectorField (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : Type*) where
  field : E → E
  contDiff : ContDiff ℝ 1 field
  invariant : E → S
  compact_fiber : ∀ q : E, IsCompact {p : E | invariant p=invariant q}
  conserved : ∀ (γ : ℝ → E) (a b : ℝ),
    (∀ t ∈ Ioo a b, HasDerivAt γ (field (γ t)) t) →
    ∀ u v : ℝ, u ∈ Ioo a b → v ∈ Ioo a b → invariant (γ u)=invariant (γ v)

namespace CompactInvariantVectorField
variable (D : CompactInvariantVectorField E S)

omit [CompleteSpace E] in
theorem exists_lipschitzOn_integralCurve (γ : ℝ → E) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (D.field (γ t)) t)
    (u : ℝ) (hu : u ∈ Ioo a b) :
    ∃ C : ℝ≥0, LipschitzOnWith C γ (Ioo a b) := by
  obtain ⟨C,hC⟩ := (D.compact_fiber (γ u)).exists_bound_of_continuousOn D.contDiff.continuous.continuousOn
  refine ⟨⟨max C 0,le_max_right _ _⟩,?_⟩
  apply (convex_Ioo a b).lipschitzOnWith_of_nnnorm_deriv_le
    (fun t ht => (hγ t ht).differentiableAt)
  intro t ht
  change ‖deriv γ t‖ ≤ max C 0
  rw [(hγ t ht).deriv]
  exact (hC (γ t) (D.conserved γ a b hγ t u ht hu)).trans (le_max_left _ _)

theorem exists_limit_of_mem_closedInterval (γ : ℝ → E) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (D.field (γ t)) t)
    (u c : ℝ) (hu : u ∈ Ioo a b) (hc : c ∈ Icc a b) :
    ∃ ψ : E, Tendsto γ (𝓝[Ioo a b] c) (𝓝 ψ) ∧ D.invariant ψ=D.invariant (γ u) := by
  obtain ⟨C,hLip⟩ := D.exists_lipschitzOn_integralCurve γ a b hγ u hu
  have hcl : c ∈ closure (Ioo a b) := by
    rw [closure_Ioo (hu.1.trans hu.2).ne]
    exact hc
  let : NeBot (𝓝[Ioo a b] c) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hCauchy : Cauchy (𝓝[Ioo a b] c) := cauchy_nhds.mono nhdsWithin_le_nhds
  obtain ⟨ψ,hψ⟩ := cauchy_map_iff_exists_tendsto.mp
    (hCauchy.map_of_le hLip.uniformContinuousOn (le_principal_iff.mpr self_mem_nhdsWithin))
  refine ⟨ψ,hψ,?_⟩
  apply (D.compact_fiber (γ u)).isClosed.mem_of_tendsto hψ
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact D.conserved γ a b hγ t u ht hu

theorem exists_rightContinuation (γ : ℝ → E) (a b : ℝ) (hab : a < b)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (D.field (γ t)) t) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Γ : ℝ → E, EqOn Γ γ (Ioo a b) ∧
      ∀ t ∈ Ioo a (b+ε), HasDerivAt Γ (D.field (Γ t)) t := by
  have hu : (a+b)/2 ∈ Ioo a b := ⟨by linarith,by linarith⟩
  obtain ⟨ψ,hlim,_⟩ := D.exists_limit_of_mem_closedInterval γ a b hγ ((a+b)/2) b hu ⟨hab.le,le_rfl⟩
  obtain ⟨η,hηb,ε,hε,hηder⟩ :=
    D.contDiff.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ (x₀ := ψ) b
  have hηlim : Tendsto η (𝓝[Ioo b (b+ε)] b) (𝓝 ψ) := by
    have h := (hηder b ⟨by linarith,by linarith⟩).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Ioo b (b+ε)] b ≤ 𝓝 b)
    simpa only [hηb] using h
  refine ⟨ε,hε,joinIntegralCurve b ψ γ η,?_,?_⟩
  · intro t ht
    exact joinIntegralCurve_of_lt b ψ γ η ht.2
  · exact hasDerivAt_joinIntegralCurve D.field γ η ψ a b (b+ε) hab (by linarith) hγ
      (fun t ht => hηder t ⟨by linarith [ht.1],ht.2⟩) hlim hηlim D.contDiff.continuous.continuousAt

theorem exists_leftContinuation (γ : ℝ → E) (a b : ℝ) (hab : a < b)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (D.field (γ t)) t) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Γ : ℝ → E, EqOn Γ γ (Ioo a b) ∧
      ∀ t ∈ Ioo (a-ε) b, HasDerivAt Γ (D.field (Γ t)) t := by
  have hu : (a+b)/2 ∈ Ioo a b := ⟨by linarith,by linarith⟩
  obtain ⟨ψ,hlim,_⟩ := D.exists_limit_of_mem_closedInterval γ a b hγ ((a+b)/2) a hu ⟨le_rfl,hab.le⟩
  obtain ⟨η,hηa,ε,hε,hηder⟩ :=
    D.contDiff.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ (x₀ := ψ) a
  have hηlim : Tendsto η (𝓝[Ioo (a-ε) a] a) (𝓝 ψ) := by
    have h := (hηder a ⟨by linarith,by linarith⟩).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Ioo (a-ε) a] a ≤ 𝓝 a)
    simpa only [hηa] using h
  refine ⟨ε,hε,joinIntegralCurve a ψ η γ,?_,?_⟩
  · intro t ht
    exact joinIntegralCurve_of_gt a ψ η γ ht.1
  · exact hasDerivAt_joinIntegralCurve D.field η γ ψ (a-ε) a b (by linarith) hab
      (fun t ht => hηder t ⟨ht.1,by linarith [ht.2]⟩) hγ hηlim hlim D.contDiff.continuous.continuousAt

end CompactInvariantVectorField
end NLS.FunctionalAnalysis
