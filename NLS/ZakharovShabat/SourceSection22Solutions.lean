import NLS.ZakharovShabat.SourceSection22SignCorrection
import NLS.ZakharovShabat.SourceSmoothApproximationSolutions

/-! # Original Section 22 phases and actual NLS solutions

For 1 < p ≤ 2 the retained original data give global solutions in the
all-smooth-approximation sense. Their coordinate laws have the Hamiltonian
signs. The printed time orientation fails that same solution definition
at constructed finite-gap sources, for both ordinary and renormalized NLS.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The same original family gives both global physical NLS solutions. -/
theorem global_physical_solutions (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    IsRenormalizedNLSSolutionOn univ φ (A.hamiltonianRenormalizedSourceFlow D.complex hp2 φ) ∧
    IsOrdinaryNLSSolutionOn univ φ (A.hamiltonianOrdinarySourceFlow D.complex hp2 φ) :=
  ⟨A.renormalizedSourceFlow_isSolution Q.roots D.roots_open D.roots_real_subset D.complex hp2 φ,
    A.ordinarySourceFlow_isSolution Q.roots D.roots_open D.roots_real_subset D.complex hp2 φ⟩

/-- Corrected Remark 22.3 in the global exponent range, for every continuous
curve on any time set containing zero. Solutions keep their original approximation definition. -/
theorem renormalized_solution_iff_coordinates (hp2 : p ≤ 2) (J : Set ℝ)
    (φ : realTypeSourceSubmodule p) (γ : ℝ → realTypeSourceSubmodule p) :
    IsRenormalizedNLSSolutionOn J φ γ ↔ 0 ∈ J ∧ ContinuousOn γ J ∧
      ∀ τ ∈ J, sourceComplexBirkhoffMap hp hp1 s (γ τ).val =
        Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) τ
          (sourceComplexBirkhoffMap hp hp1 s φ.val) := by
  have hsol := (Q.global_physical_solutions hp2 φ).1
  constructor
  · intro hγ
    refine ⟨hγ.zero_mem,hγ.continuous,?_⟩
    intro τ hτ
    rw [hγ.eqOn_inter hsol hp hp1 ⟨hτ,mem_univ _⟩]
    exact A.complex_map_hamiltonianRenormalizedSourceFlow D.complex hp2 φ τ
  · rintro ⟨h0,hc,he⟩
    have hsame : EqOn γ (A.hamiltonianRenormalizedSourceFlow D.complex hp2 φ) J := by
      intro τ hτ
      apply D.complex.complex_map_real_injective
      exact (he τ hτ).trans (A.complex_map_hamiltonianRenormalizedSourceFlow D.complex hp2 φ τ).symm
    refine ⟨h0,hc,?_,?_⟩
    · rw [hsame h0,A.hamiltonianRenormalizedSourceFlow_zero]
    · intro f hf τ hτ
      rw [hsame hτ]
      exact hsol.approximation f hf τ (mem_univ _)

/-- The analogous ordinary phase characterization includes the actual physical mass. -/
theorem ordinary_solution_iff_coordinates (hp2 : p ≤ 2) (J : Set ℝ)
    (φ : realTypeSourceSubmodule p) (γ : ℝ → realTypeSourceSubmodule p) :
    IsOrdinaryNLSSolutionOn J φ γ ↔ 0 ∈ J ∧ ContinuousOn γ J ∧
      ∀ τ ∈ J, sourceComplexBirkhoffMap hp hp1 s (γ τ).val =
        Birkhoff.hamiltonianPhaseFlow (A.ordinaryPhaseFrequency hp2 φ) τ
          (sourceComplexBirkhoffMap hp hp1 s φ.val) := by
  have hsol := (Q.global_physical_solutions hp2 φ).2
  constructor
  · intro hγ
    refine ⟨hγ.zero_mem,hγ.continuous,?_⟩
    intro τ hτ
    rw [hγ.eqOn_inter hsol hp hp1 ⟨hτ,mem_univ _⟩]
    exact A.complex_map_hamiltonianOrdinarySourceFlow D.complex hp2 φ τ
  · rintro ⟨h0,hc,he⟩
    have hsame : EqOn γ (A.hamiltonianOrdinarySourceFlow D.complex hp2 φ) J := by
      intro τ hτ
      apply D.complex.complex_map_real_injective
      exact (he τ hτ).trans (A.complex_map_hamiltonianOrdinarySourceFlow D.complex hp2 φ τ).symm
    refine ⟨h0,hc,?_,?_⟩
    · rw [hsame h0,A.hamiltonianOrdinarySourceFlow_zero]
    · intro f hf τ hτ
      rw [hsame hτ]
      exact hsol.approximation f hf τ (mem_univ _)

/-- Both literal printed source flows fail the physical solution definition
at the same actual original finite-gap source. -/
theorem printed_flows_not_physical_solutions (hp2 : p ≤ 2) (n : ℤ) (hn : n ≠ 0) :
    ∃ φ : realTypeSourceSubmodule p, φ ∈ sourceFiniteGapLocus hp hp1 ∧
      0 < A.phaseFrequency φ n ∧
      (¬ IsRenormalizedNLSSolutionOn univ φ (A.renormalizedSourceFlow D.complex hp2 φ)) ∧
      (¬ IsOrdinaryNLSSolutionOn univ φ (A.ordinarySourceFlow D.complex hp2 φ)) := by
  obtain ⟨φ,hf,hω,hz,_⟩ := Q.exists_finiteGap_positive_phase n hn
  refine ⟨φ,hf,hω,?_,?_⟩
  · intro hbad
    have he (τ : ℝ) : A.renormalizedPhaseTrajectory s φ τ =
        Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) τ
          (sourceComplexBirkhoffMap hp hp1 s φ.val) := by
      rw [← A.complex_map_renormalizedSourceFlow D.complex hp2]
      exact ((Q.renormalized_solution_iff_coordinates hp2 univ φ _).mp hbad).2.2 τ (mem_univ _)
    apply Birkhoff.not_hasDerivAt_printedPhaseFlow_hamiltonian _ _ n hω.ne' hz
    change HasDerivAt (fun τ => (A.renormalizedPhaseTrajectory s φ τ).1 n) _ 0
    simpa only [he,Birkhoff.hamiltonianPhaseFlow_zero] using!
      Birkhoff.hasDerivAt_hamiltonianPhaseFlow_fst (A.phaseFrequency φ)
        (sourceComplexBirkhoffMap hp hp1 s φ.val) n 0
  · intro hbad
    have hm : 0 ≤ sourceOrdinaryMass hp2 φ := by
      rw [sourceOrdinaryMass_eq_tsum hp hp1]
      exact tsum_nonneg (fun k => (sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero
        hp hp1 k φ.val φ.property).1)
    have hωo : 0 < A.ordinaryPhaseFrequency hp2 φ n := by
      change 0 < A.phaseFrequency φ n+4*sourceOrdinaryMass hp2 φ
      positivity
    have he (τ : ℝ) : A.ordinaryPhaseTrajectory s hp2 φ τ =
        Birkhoff.hamiltonianPhaseFlow (A.ordinaryPhaseFrequency hp2 φ) τ
          (sourceComplexBirkhoffMap hp hp1 s φ.val) := by
      rw [← A.complex_map_ordinarySourceFlow D.complex hp2]
      exact ((Q.ordinary_solution_iff_coordinates hp2 univ φ _).mp hbad).2.2 τ (mem_univ _)
    apply Birkhoff.not_hasDerivAt_printedPhaseFlow_hamiltonian _ _ n hωo.ne' hz
    change HasDerivAt (fun τ => (A.ordinaryPhaseTrajectory s hp2 φ τ).1 n) _ 0
    simpa only [he,Birkhoff.hamiltonianPhaseFlow_zero] using!
      Birkhoff.hasDerivAt_hamiltonianPhaseFlow_fst (A.ordinaryPhaseFrequency hp2 φ)
        (sourceComplexBirkhoffMap hp hp1 s φ.val) n 0

end NLS.ZakharovShabat.SourceSection20Data
