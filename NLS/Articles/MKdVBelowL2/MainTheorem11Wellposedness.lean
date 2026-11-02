import NLS.Articles.MKdVBelowL2.ScalarClassicalFourthAdapter
import NLS.Articles.MKdVBelowL2.ScalarSmoothFourierApproximation

/-! # The local and small-data wellposedness clauses of Theorem 1.1

The smooth solution map may be any map representing classical physical
solutions. Its uniqueness and agreement with the fixed Birkhoff lift have
been proved. The approximation definition quantifies over every genuinely
smooth real sequence converging in the original physical Fourier norm.
The original unrenormalized fixed-time nonextension clause is separate.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A choice of the canonical smooth physical mKdV solution at each smooth datum. -/
def IsClassicalScalarSolutionMap
    (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p) : Prop :=
  ∀ u : PhysicalScalarRealInput p, IsSmoothPhysicalScalarInput u →
    IsClassicalPhysicalScalarTrajectory u (S u)

/-- The article's solution definition on a compact time interval. Continuity
is built into the path type; convergence is required for every smooth sequence. -/
def IsMKdVSolutionBySmoothApproximation
    (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p)
    (T : ℝ) (hT : 0 ≤ T) (u : PhysicalScalarRealInput p)
    (γ : C(Icc (-T) T,PhysicalScalarRealInput p)) : Prop :=
  γ ⟨0,by constructor <;> linarith⟩ = u ∧
    ∀ v : ℕ → PhysicalScalarRealInput p, (∀ N, IsSmoothPhysicalScalarInput (v N)) →
      Tendsto v atTop (𝓝 u) → ∀ time : Icc (-T) T,
        Tendsto (fun N => S (v N) time.val) atTop (𝓝 (γ time))

/-- A classical smooth solution map exists, and is this same fixed lift
wherever the datum is smooth. -/
theorem isClassicalScalarSolutionMap_fourthScalarImageFlow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) :
    IsClassicalScalarSolutionMap (fourthScalarImageFlow hp hp1) :=
  fun u hu => isClassicalPhysicalScalarTrajectory_fourthScalarImageFlow hp hp1 h2p u hu

/-- Any classical smooth solution map yields uniform convergence of all
smooth approximants on every admissible compact interval. -/
theorem tendstoUniformly_classicalScalarSolutionMap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p)
    (hS : IsClassicalScalarSolutionMap S) (T : ℝ)
    (v : ℕ → PhysicalScalarRealInput p) (u : PhysicalScalarRealInput p)
    (hs : ∀ N, IsSmoothPhysicalScalarInput (v N))
    (hu : u ∈ fourthScalarTrajectoryDomain hp hp1 T) (hv : Tendsto v atTop (𝓝 u)) :
    TendstoUniformly (fun N (time : Icc (-T) T) => S (v N) time.val)
      (fun time => fourthScalarImageFlow hp hp1 u time.val) atTop := by
  have he : (fun N (time : Icc (-T) T) => S (v N) time.val) =
      fun N time => fourthScalarImageFlow hp hp1 (v N) time.val := by
    funext N time
    exact congrFun (fourthScalarImageFlow_eq_of_classical hp hp1 h2p (v N) (hs N) (S (v N)) (hS _ (hs N))) time.val
  rw [he]
  exact (tendstoUniformly_fourthScalarImageFlow_of_smooth hp hp1 h2p T v u hs hu hv).1

/-- The approximation definition characterizes exactly the actual scalar
lift. Smooth sequences exist at every datum, making uniqueness nonvacuous. -/
theorem isMKdVSolutionBySmoothApproximation_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p)
    (hS : IsClassicalScalarSolutionMap S) (T : ℝ) (hT : 0 ≤ T)
    (u : PhysicalScalarRealInput p) (hu : u ∈ fourthScalarTrajectoryDomain hp hp1 T)
    (γ : C(Icc (-T) T,PhysicalScalarRealInput p)) :
    IsMKdVSolutionBySmoothApproximation S T hT u γ ↔ γ = fourthScalarTrajectoryOn hp hp1 T u := by
  constructor
  · intro hγ
    have he := fourthScalarImageFlow_unique_smooth_approximation hp hp1 T u hu γ (fun v hs hv time => by
      have h := hγ.2 v hs hv time
      have heq : (fun N => S (v N) time.val) =
          fun N => fourthScalarImageFlow hp hp1 (v N) time.val := by
        funext N
        exact congrFun (fourthScalarImageFlow_eq_of_classical hp hp1 h2p (v N) (hs N) (S (v N)) (hS _ (hs N))) time.val
      rwa [heq] at h)
    apply ContinuousMap.ext
    intro time
    exact (congrFun he time).trans (fourthScalarTrajectoryOn_apply hp hp1 T u hu time).symm
  · rintro rfl
    constructor
    · rw [fourthScalarTrajectoryOn_apply hp hp1 T u hu,fourthScalarImageFlow_zero]
    · intro v hs hv time
      rw [fourthScalarTrajectoryOn_apply hp hp1 T u hu]
      exact (tendstoUniformly_classicalScalarSolutionMap hp hp1 h2p S hS T v u hs hu hv).tendsto_at time

/-- The local C⁰-wellposedness clause of source Theorem 1.1, in the
original real scalar Fourier norm and the full uniform trajectory norm. -/
theorem theorem1_1_local_classical_approximation
    (hp : p ≠ ⊤) (h2p : 2 < p)
    (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p)
    (hS : IsClassicalScalarSolutionMap S) (u : PhysicalScalarRealInput p) :
    ∃ (T : ℝ) (hT : 0 < T), ∃ U : Set (PhysicalScalarRealInput p), IsOpen U ∧ u ∈ U ∧
      ContinuousOn (fourthScalarTrajectoryOn hp (lt_trans (by norm_num) h2p) T) U ∧
      ∀ v ∈ U, ∃! γ : C(Icc (-T) T,PhysicalScalarRealInput p),
        IsMKdVSolutionBySmoothApproximation S T hT.le v γ := by
  let hp1 : 1 < p := lt_trans (by norm_num) h2p
  obtain ⟨T,hT,U,hU,hu,hdom,hcont⟩ := exists_local_fourthScalarTrajectory hp hp1 u
  refine ⟨T,hT,U,hU,hu,hcont,fun v hv => ?_⟩
  have hi := isMKdVSolutionBySmoothApproximation_iff hp hp1 h2p.le S hS T hT.le v (hdom hv)
  exact ⟨fourthScalarTrajectoryOn hp hp1 T v,(hi _).mpr rfl,fun γ hγ => (hi γ).mp hγ⟩

/-- A single invariant open neighborhood of zero works for every compact
time interval, with classical smooth approximation and uniform path continuity. -/
theorem theorem1_1_small_global_classical_approximation
    (hp : p ≠ ⊤) (h2p : 2 < p)
    (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p)
    (hS : IsClassicalScalarSolutionMap S) :
    ∃ U : Set (PhysicalScalarRealInput p), IsOpen U ∧ (0 : PhysicalScalarRealInput p) ∈ U ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ContinuousOn (fourthScalarTrajectoryOn hp (lt_trans (by norm_num) h2p) T) U ∧
        ∀ v ∈ U, ∃! γ : C(Icc (-T) T,PhysicalScalarRealInput p),
          IsMKdVSolutionBySmoothApproximation S T hT.le v γ) ∧
      ∀ v ∈ U, ∀ t : ℝ, fourthScalarImageFlow hp (lt_trans (by norm_num) h2p) v t ∈ U := by
  let hp1 : 1 < p := lt_trans (by norm_num) h2p
  obtain ⟨U,hU,hzero,hdom,hinv⟩ := exists_global_small_fourthScalarTrajectory hp hp1
  refine ⟨U,hU,hzero,fun T hT => ⟨(hdom T).2,fun v hv => ?_⟩,hinv⟩
  have hi := isMKdVSolutionBySmoothApproximation_iff hp hp1 h2p.le S hS T hT.le v ((hdom T).1 hv)
  exact ⟨fourthScalarTrajectoryOn hp hp1 T v,(hi _).mpr rfl,fun γ hγ => (hi γ).mp hγ⟩

end NLS.Articles.MKdVBelowL2
