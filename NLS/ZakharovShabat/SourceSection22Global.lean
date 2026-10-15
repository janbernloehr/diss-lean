import NLS.ZakharovShabat.SourceSection22Solutions
import NLS.ZakharovShabat.AnalyticNLSWellposedness

/-! # Global analytic original flows in the surjective exponent range

For 1 < p ≤ 2, the same original family gives the two physical flows,
analytic compact-time source trajectories, their group laws, and analytic
coordinate time maps with analytic inverses. The coordinate maps use the
original Birkhoff homeomorphism, not a separately chosen family.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- Both physical source trajectories are analytic in the full uniform compact-time norm. -/
theorem global_physical_trajectories (hp2 : p ≤ 2) (T : ℝ) :
    AnalyticOnNhd ℝ
      (A.hamiltonianRenormalizedSourceTrajectoryOn Q.roots D.roots_open D.roots_real_subset D.complex hp2 T) univ ∧
    AnalyticOnNhd ℝ
      (A.hamiltonianOrdinarySourceTrajectoryOn Q.roots D.roots_open D.roots_real_subset D.complex hp2 T) univ :=
  ⟨A.analytic_hamiltonianRenormalizedSourceTrajectoryOn Q.roots D.roots_open D.roots_real_subset D.complex hp2 T,
    A.analytic_hamiltonianOrdinarySourceTrajectoryOn Q.roots D.roots_open D.roots_real_subset D.complex hp2 T⟩

/-- The original physical flows satisfy both group laws for every real time. -/
theorem global_physical_group (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (τ σ : ℝ) :
    A.hamiltonianRenormalizedSourceFlow D.complex hp2
      (A.hamiltonianRenormalizedSourceFlow D.complex hp2 φ σ) τ =
        A.hamiltonianRenormalizedSourceFlow D.complex hp2 φ (τ+σ) ∧
    A.hamiltonianOrdinarySourceFlow D.complex hp2
      (A.hamiltonianOrdinarySourceFlow D.complex hp2 φ σ) τ =
        A.hamiltonianOrdinarySourceFlow D.complex hp2 φ (τ+σ) :=
  ⟨A.hamiltonianRenormalizedSourceFlow_add Q.roots.toSourcePsiIsolatingComplexExtension D.complex hp2 φ τ σ,
    A.hamiltonianOrdinarySourceFlow_add Q.roots.toSourcePsiIsolatingComplexExtension D.complex hp2 φ τ σ⟩

/-- Corollary 22.2(i) in the original smooth-approximation solution sense,
with the retained original flows as the actual witnesses. -/
theorem global_analytic_wellposedness (hp2 : p ≤ 2) :
    IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.renormalizedSource p) univ ∧
    IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.ordinarySource p) univ := by
  constructor
  · refine ⟨isOpen_univ,A.hamiltonianRenormalizedSourceFlow D.complex hp2,
      fun φ _ => (Q.global_physical_solutions hp2 φ).1,?_⟩
    intro T _
    exact ⟨A.hamiltonianRenormalizedSourceTrajectoryOn Q.roots D.roots_open D.roots_real_subset D.complex hp2 T,
      (Q.global_physical_trajectories hp2 T).1,fun _ _ _ => rfl⟩
  · refine ⟨isOpen_univ,A.hamiltonianOrdinarySourceFlow D.complex hp2,
      fun φ _ => (Q.global_physical_solutions hp2 φ).2,?_⟩
    intro T _
    exact ⟨A.hamiltonianOrdinarySourceTrajectoryOn Q.roots D.roots_open D.roots_real_subset D.complex hp2 T,
      (Q.global_physical_trajectories hp2 T).2,fun _ _ _ => rfl⟩

/-- Theorem 22.1(i): the physical renormalized coordinate time map is a real
analytic diffeomorphism of the full real coordinate space when p ≤ 2. -/
theorem renormalized_coordinate_time_map (hp2 : p ≤ 2) (τ : ℝ) :
    ∃ e : (RealCoeff p × RealCoeff p) ≃ₜ (RealCoeff p × RealCoeff p),
      (∀ z, Birkhoff.encodeReal (e z) =
        Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency ((D.complex.realHomeomorph hp2).symm z)) τ
          (Birkhoff.encodeReal z)) ∧
      (∀ z, Birkhoff.encodeReal (e.symm z) =
        Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency ((D.complex.realHomeomorph hp2).symm z)) (-τ)
          (Birkhoff.encodeReal z)) ∧
      AnalyticOnNhd ℝ e univ ∧ AnalyticOnNhd ℝ e.symm univ := by
  let eB := D.complex.realHomeomorph hp2
  let eS := A.renormalizedSourceHomeomorph Q.roots D.roots_open D.roots_real_subset D.complex hp2 (-τ)
  have hS := A.renormalizedSourceHomeomorph_analytic Q.roots D.roots_open D.roots_real_subset D.complex hp2 (-τ)
  refine ⟨eB.symm.trans (eS.trans eB),?_,?_,?_,?_⟩
  · intro z
    change Birkhoff.encodeReal (sourceRealBirkhoffMap hp hp1 s
      (A.hamiltonianRenormalizedSourceFlow D.complex hp2 (eB.symm z) τ)) = _
    rw [D.complex.encode_real_map,A.complex_map_hamiltonianRenormalizedSourceFlow,
      ← D.complex.encode_real_map]
    change Birkhoff.hamiltonianPhaseFlow _ _ (Birkhoff.encodeReal (eB (eB.symm z))) = _
    rw [eB.apply_symm_apply]
  · intro z
    change Birkhoff.encodeReal (sourceRealBirkhoffMap hp hp1 s
      (A.hamiltonianRenormalizedSourceFlow D.complex hp2 (eB.symm z) (-τ))) = _
    rw [D.complex.encode_real_map,A.complex_map_hamiltonianRenormalizedSourceFlow,
      ← D.complex.encode_real_map]
    change Birkhoff.hamiltonianPhaseFlow _ _ (Birkhoff.encodeReal (eB (eB.symm z))) = _
    rw [eB.apply_symm_apply]
  · intro z _
    exact (D.complex.real_map_analytic _ (mem_univ _)).comp
      ((hS.1 _ (mem_univ _)).comp (D.complex.realHomeomorph_symm_analytic hp2 z (mem_univ _)))
  · intro z _
    exact (D.complex.real_map_analytic _ (mem_univ _)).comp
      ((hS.2 _ (mem_univ _)).comp (D.complex.realHomeomorph_symm_analytic hp2 z (mem_univ _)))

/-- Theorem 22.1(ii): ordinary coordinate time maps have the same global
bi-analytic property, retaining the physical mass correction. -/
theorem ordinary_coordinate_time_map (hp2 : p ≤ 2) (τ : ℝ) :
    ∃ e : (RealCoeff p × RealCoeff p) ≃ₜ (RealCoeff p × RealCoeff p),
      (∀ z, Birkhoff.encodeReal (e z) =
        Birkhoff.hamiltonianPhaseFlow (A.ordinaryPhaseFrequency hp2 ((D.complex.realHomeomorph hp2).symm z)) τ
          (Birkhoff.encodeReal z)) ∧
      (∀ z, Birkhoff.encodeReal (e.symm z) =
        Birkhoff.hamiltonianPhaseFlow (A.ordinaryPhaseFrequency hp2 ((D.complex.realHomeomorph hp2).symm z)) (-τ)
          (Birkhoff.encodeReal z)) ∧
      AnalyticOnNhd ℝ e univ ∧ AnalyticOnNhd ℝ e.symm univ := by
  let eB := D.complex.realHomeomorph hp2
  let eS := A.ordinarySourceHomeomorph Q.roots D.roots_open D.roots_real_subset D.complex hp2 (-τ)
  have hS := A.ordinarySourceHomeomorph_analytic Q.roots D.roots_open D.roots_real_subset D.complex hp2 (-τ)
  refine ⟨eB.symm.trans (eS.trans eB),?_,?_,?_,?_⟩
  · intro z
    change Birkhoff.encodeReal (sourceRealBirkhoffMap hp hp1 s
      (A.hamiltonianOrdinarySourceFlow D.complex hp2 (eB.symm z) τ)) = _
    rw [D.complex.encode_real_map,A.complex_map_hamiltonianOrdinarySourceFlow,
      ← D.complex.encode_real_map]
    change Birkhoff.hamiltonianPhaseFlow _ _ (Birkhoff.encodeReal (eB (eB.symm z))) = _
    rw [eB.apply_symm_apply]
  · intro z
    change Birkhoff.encodeReal (sourceRealBirkhoffMap hp hp1 s
      (A.hamiltonianOrdinarySourceFlow D.complex hp2 (eB.symm z) (-τ))) = _
    rw [D.complex.encode_real_map,A.complex_map_hamiltonianOrdinarySourceFlow,
      ← D.complex.encode_real_map]
    change Birkhoff.hamiltonianPhaseFlow _ _ (Birkhoff.encodeReal (eB (eB.symm z))) = _
    rw [eB.apply_symm_apply]
  · intro z _
    exact (D.complex.real_map_analytic _ (mem_univ _)).comp
      ((hS.1 _ (mem_univ _)).comp (D.complex.realHomeomorph_symm_analytic hp2 z (mem_univ _)))
  · intro z _
    exact (D.complex.real_map_analytic _ (mem_univ _)).comp
      ((hS.2 _ (mem_univ _)).comp (D.complex.realHomeomorph_symm_analytic hp2 z (mem_univ _)))

/-- Both physical source flows are jointly continuous in time and initial source. -/
theorem global_physical_joint_continuous (hp2 : p ≤ 2) :
    Continuous (fun x : ℝ × realTypeSourceSubmodule p =>
      A.hamiltonianRenormalizedSourceFlow D.complex hp2 x.2 x.1) ∧
    Continuous (fun x : ℝ × realTypeSourceSubmodule p =>
      A.hamiltonianOrdinarySourceFlow D.complex hp2 x.2 x.1) :=
  ⟨A.continuous_hamiltonianRenormalizedSourceFlow Q.roots D.roots_open D.roots_real_subset D.complex hp2,
    A.continuous_hamiltonianOrdinarySourceFlow Q.roots D.roots_open D.roots_real_subset D.complex hp2⟩

/-- Theorem 22.1(ii) has analyticity in the entire compact-time coordinate norm. -/
theorem ordinary_coordinate_trajectory_analytic (hp2 : p ≤ 2) (T : ℝ) :
    AnalyticOnNhd ℝ (fun z : RealCoeff p × RealCoeff p =>
      (A.ordinaryPhaseTrajectoryOn Q.roots D.roots_open D.roots_real_subset D.complex hp2 T
        ((D.complex.realHomeomorph hp2).symm z)).comp (hamiltonianTimeReflection T)) univ := by
  intro z _
  exact ((ContinuousMap.compCLM ℝ (Coeff p × Coeff p) (hamiltonianTimeReflection T)).analyticAt _).comp
    (A.analytic_ordinaryPhaseTrajectoryOn_coordinates Q.roots D.roots_open D.roots_real_subset
      D.complex hp2 T z (mem_univ _))

/-- Evaluation of the analytic ordinary path retains the original coordinates and mass. -/
theorem ordinary_coordinate_trajectory_apply (hp2 : p ≤ 2) (T : ℝ)
    (z : RealCoeff p × RealCoeff p) (τ : Icc (-T) T) :
    ((A.ordinaryPhaseTrajectoryOn Q.roots D.roots_open D.roots_real_subset D.complex hp2 T
      ((D.complex.realHomeomorph hp2).symm z)).comp (hamiltonianTimeReflection T)) τ =
        Birkhoff.hamiltonianPhaseFlow (A.ordinaryPhaseFrequency hp2 ((D.complex.realHomeomorph hp2).symm z))
          τ.val (Birkhoff.encodeReal z) := by
  change Birkhoff.hamiltonianPhaseFlow _ _
    (sourceComplexBirkhoffMap hp hp1 s ((D.complex.realHomeomorph hp2).symm z).val) = _
  rw [← D.complex.encode_real_map]
  change Birkhoff.hamiltonianPhaseFlow _ _
    (Birkhoff.encodeReal ((D.complex.realHomeomorph hp2) ((D.complex.realHomeomorph hp2).symm z))) = _
  rw [Homeomorph.apply_symm_apply]

end NLS.ZakharovShabat.SourceSection20Data
