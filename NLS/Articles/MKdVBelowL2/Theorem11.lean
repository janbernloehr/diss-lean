import NLS.Articles.MKdVBelowL2.MainTheorem11Wellposedness
import NLS.Articles.MKdVBelowL2.OrdinaryMKdVFixedTimeNonextension

/-! # Article Theorem 1.1

For every finite p>2, the renormalized physical mKdV equation is locally
C⁰-wellposed at every original real scalar Fourier–Lebesgue datum, and
globally C⁰-wellposed on one invariant open neighborhood of zero. Continuous
paths use the full uniform norm and the article's all-smooth-sequences
solution definition. The canonical ordinary smooth physical map has no
continuous extension to any non-L² datum at any selected positive time.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One invariant zero neighborhood carries actual global continuous
solution curves with the all-smooth-sequences property at every real time.
The named continuous compact-path map supplies each unique solution. -/
theorem theorem1_1_small_global_curves (hp : p ≠ ⊤) (h2p : 2 < p)
    (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p)
    (hS : IsClassicalScalarSolutionMap S) :
    let hp1 : 1 < p := lt_trans (by norm_num) h2p
    ∃ U : Set (PhysicalScalarRealInput p), IsOpen U ∧ (0 : PhysicalScalarRealInput p) ∈ U ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ContinuousOn (fourthScalarTrajectoryOn hp hp1 T) U ∧
        ∀ v ∈ U,
          IsMKdVSolutionBySmoothApproximation S T hT.le v (fourthScalarTrajectoryOn hp hp1 T v) ∧
          ∃! γ : C(Icc (-T) T,PhysicalScalarRealInput p),
            IsMKdVSolutionBySmoothApproximation S T hT.le v γ) ∧
      (∀ v ∈ U, Continuous (fun time : ℝ => fourthScalarImageFlow hp hp1 v time) ∧
        ∀ w : ℕ → PhysicalScalarRealInput p, (∀ N, IsSmoothPhysicalScalarInput (w N)) →
          Tendsto w atTop (𝓝 v) → ∀ time : ℝ,
            Tendsto (fun N => S (w N) time) atTop (𝓝 (fourthScalarImageFlow hp hp1 v time))) ∧
      ∀ v ∈ U, ∀ t : ℝ, fourthScalarImageFlow hp hp1 v t ∈ U := by
  dsimp only
  let hp1 : 1 < p := lt_trans (by norm_num) h2p
  obtain ⟨U,hU,hzero,hdom,hinv⟩ := exists_global_small_fourthScalarTrajectory hp hp1
  refine ⟨U,hU,hzero,?_,?_,hinv⟩
  · intro T hT
    refine ⟨(hdom T).2,fun v hv => ?_⟩
    have hi := isMKdVSolutionBySmoothApproximation_iff hp hp1 h2p.le S hS T hT.le v ((hdom T).1 hv)
    exact ⟨(hi _).mpr rfl,
      fourthScalarTrajectoryOn hp hp1 T v,(hi _).mpr rfl,fun γ hγ => (hi γ).mp hγ⟩
  · intro v hv
    have htime (r : ℝ) : (r,v) ∈ fourthScalarImageDomain hp hp1 :=
      (hdom |r|).1 hv ⟨r,neg_abs_le r,le_abs_self r⟩
    refine ⟨(continuousOn_fourthScalarImageFlow hp hp1).comp_continuous
      (f := fun r : ℝ => (r,v)) (continuous_id.prodMk continuous_const) htime,?_⟩
    intro w hs hw time
    exact (tendstoUniformly_classicalScalarSolutionMap hp hp1 h2p.le S hS |time| w v hs
      ((hdom |time|).1 hv) hw).tendsto_at ⟨time,neg_abs_le time,le_abs_self time⟩

/-- Theorem 1.1, including the fixed-time nonextension consequence for the
original equation. The named continuous local and compact global path maps
are explicitly the unique smooth-approximation solutions. Both smooth maps
exist as actual classical physical PDE maps, and classical uniqueness
removes any dependence on those choices. -/
theorem theorem1_1 (hp : p ≠ ⊤) (h2p : 2 < p) :
    let hp1 : 1 < p := lt_trans (by norm_num) h2p
    ∃ Sren Sord : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p,
      IsClassicalScalarSolutionMap Sren ∧ IsClassicalOrdinaryScalarSolutionMap Sord ∧
      (∀ u : PhysicalScalarRealInput p,
        ∃ (T : ℝ) (hT : 0 < T), ∃ U : Set (PhysicalScalarRealInput p), IsOpen U ∧ u ∈ U ∧
          ContinuousOn (fourthScalarTrajectoryOn hp hp1 T) U ∧
          ∀ v ∈ U,
            IsMKdVSolutionBySmoothApproximation Sren T hT.le v (fourthScalarTrajectoryOn hp hp1 T v) ∧
            ∃! γ : C(Icc (-T) T,PhysicalScalarRealInput p),
              IsMKdVSolutionBySmoothApproximation Sren T hT.le v γ) ∧
      (∃ U : Set (PhysicalScalarRealInput p), IsOpen U ∧ (0 : PhysicalScalarRealInput p) ∈ U ∧
        (∀ T : ℝ, ∀ hT : 0 < T,
          ContinuousOn (fourthScalarTrajectoryOn hp hp1 T) U ∧
          ∀ v ∈ U,
            IsMKdVSolutionBySmoothApproximation Sren T hT.le v (fourthScalarTrajectoryOn hp hp1 T v) ∧
            ∃! γ : C(Icc (-T) T,PhysicalScalarRealInput p),
              IsMKdVSolutionBySmoothApproximation Sren T hT.le v γ) ∧
        (∀ v ∈ U, Continuous (fun time : ℝ => fourthScalarImageFlow hp hp1 v time) ∧
          ∀ w : ℕ → PhysicalScalarRealInput p, (∀ N, IsSmoothPhysicalScalarInput (w N)) →
            Tendsto w atTop (𝓝 v) → ∀ time : ℝ,
              Tendsto (fun N => Sren (w N) time) atTop (𝓝 (fourthScalarImageFlow hp hp1 v time))) ∧
        ∀ v ∈ U, ∀ t : ℝ, fourthScalarImageFlow hp hp1 v t ∈ U) ∧
      ∀ u : PhysicalScalarRealInput p, u ∉ physicalScalarL2Locus p →
        ∀ time : ℝ, 0 < time → ∀ E : PhysicalScalarRealInput p → PhysicalScalarRealInput p,
          (∀ v : PhysicalScalarRealInput p, IsSmoothPhysicalScalarInput v → E v = Sord v time) →
          ¬ ContinuousWithinAt E ({v | IsSmoothPhysicalScalarInput v} ∪ {u}) u := by
  dsimp only
  let hp1 : 1 < p := lt_trans (by norm_num) h2p
  let Sren := fourthScalarImageFlow hp hp1
  have hren : IsClassicalScalarSolutionMap Sren :=
    isClassicalScalarSolutionMap_fourthScalarImageFlow hp hp1 h2p.le
  obtain ⟨Sord,hord⟩ := exists_classicalOrdinaryScalarSolutionMap (p := p) h2p.le
  exact ⟨Sren,Sord,hren,hord,
    theorem1_1_local_classical_approximation hp h2p Sren hren,
    theorem1_1_small_global_curves hp h2p Sren hren,
    fun u hu time ht E hE => theorem1_1_fixed_time_no_smooth_extension hp h2p Sord hord u hu time ht E hE⟩

end NLS.Articles.MKdVBelowL2
