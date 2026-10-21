import NLS.Dynamics.RectangularHamiltonianOscillators
import NLS.ZakharovShabat.SourceSection22Original

/-! # Oscillators and conserved frequencies along original solutions

This implements the original dynamics statements in the introduction, printed p. 9.
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

/-- Every original ordinary solution has the same actual rectangular phase trajectory. -/
theorem ordinary_original_rectangular_phase (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsOrdinaryNLSSolutionOn univ φ γ) (τ : ℝ) :
    sourceRealBirkhoffMap hp hp1 s (γ τ) =
      Birkhoff.decodeReal (Birkhoff.hamiltonianPhaseFlow (A.ordinaryPhaseFrequency hp2 φ) τ
        (sourceComplexBirkhoffMap hp hp1 s φ.val)) := by
  have he := hγ.eqOn_inter (Q.global_physical_solutions hp2 φ).2 hp hp1
    ⟨mem_univ τ,mem_univ τ⟩
  rw [he,← Birkhoff.decodeReal_encodeReal (sourceRealBirkhoffMap hp hp1 s _),
    D.complex.encode_real_map,A.complex_map_hamiltonianOrdinarySourceFlow]

/-- Every original renormalized solution retains the same actual rectangular phase trajectory. -/
theorem renormalized_original_rectangular_phase (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsRenormalizedNLSSolutionOn univ φ γ) (τ : ℝ) :
    sourceRealBirkhoffMap hp hp1 s (γ τ) =
      Birkhoff.decodeReal (Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) τ
        (sourceComplexBirkhoffMap hp hp1 s φ.val)) := by
  have he := hγ.eqOn_inter (Q.global_physical_solutions hp2 φ).1 hp hp1
    ⟨mem_univ τ,mem_univ τ⟩
  rw [he,← Birkhoff.decodeReal_encodeReal (sourceRealBirkhoffMap hp hp1 s _),
    D.complex.encode_real_map,A.complex_map_hamiltonianRenormalizedSourceFlow]

/-- The introduction's literal rectangular oscillator equations hold along every ordinary solution. -/
theorem ordinary_original_rectangular_oscillators (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsOrdinaryNLSSolutionOn univ φ γ) (τ : ℝ) (n : ℤ) :
    HasDerivAt (fun σ => (sourceRealBirkhoffMap hp hp1 s (γ σ)).1 n)
      (-A.ordinaryPhaseFrequency hp2 φ n*(sourceRealBirkhoffMap hp hp1 s (γ τ)).2 n) τ ∧
    HasDerivAt (fun σ => (sourceRealBirkhoffMap hp hp1 s (γ σ)).2 n)
      (A.ordinaryPhaseFrequency hp2 φ n*(sourceRealBirkhoffMap hp hp1 s (γ τ)).1 n) τ := by
  simp only [Q.ordinary_original_rectangular_phase hp2 hγ]
  exact ⟨Birkhoff.hasDerivAt_rectangularHamiltonianPhase_fst _ _ n τ,
    Birkhoff.hasDerivAt_rectangularHamiltonianPhase_snd _ _ n τ⟩

/-- The same equations hold for the renormalized physical flow with its retained frequencies. -/
theorem renormalized_original_rectangular_oscillators (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsRenormalizedNLSSolutionOn univ φ γ) (τ : ℝ) (n : ℤ) :
    HasDerivAt (fun σ => (sourceRealBirkhoffMap hp hp1 s (γ σ)).1 n)
      (-A.phaseFrequency φ n*(sourceRealBirkhoffMap hp hp1 s (γ τ)).2 n) τ ∧
    HasDerivAt (fun σ => (sourceRealBirkhoffMap hp hp1 s (γ σ)).2 n)
      (A.phaseFrequency φ n*(sourceRealBirkhoffMap hp hp1 s (γ τ)).1 n) τ := by
  simp only [Q.renormalized_original_rectangular_phase hp2 hγ]
  exact ⟨Birkhoff.hasDerivAt_rectangularHamiltonianPhase_fst _ _ n τ,
    Birkhoff.hasDerivAt_rectangularHamiltonianPhase_snd _ _ n τ⟩

/-- The ordinary oscillator frequencies are the same at every point of the original solution. -/
theorem ordinary_original_frequency_conserved (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsOrdinaryNLSSolutionOn univ φ γ) (τ : ℝ) :
    A.ordinaryPhaseFrequency hp2 (γ τ) = A.ordinaryPhaseFrequency hp2 φ := by
  have he := hγ.eqOn_inter (Q.global_physical_solutions hp2 φ).2 hp hp1
    ⟨mem_univ τ,mem_univ τ⟩
  rw [he]
  exact A.ordinaryPhaseFrequency_ordinarySourceFlow Q.roots.toSourcePsiIsolatingComplexExtension
    D.complex hp2 φ (-τ)

/-- The renormalized oscillator frequencies are constant along the same original solution. -/
theorem renormalized_original_frequency_conserved (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsRenormalizedNLSSolutionOn univ φ γ) (τ : ℝ) :
    A.phaseFrequency (γ τ) = A.phaseFrequency φ := by
  have he := hγ.eqOn_inter (Q.global_physical_solutions hp2 φ).1 hp hp1
    ⟨mem_univ τ,mem_univ τ⟩
  rw [he]
  exact A.phaseFrequency_renormalizedSourceFlow Q.roots.toSourcePsiIsolatingComplexExtension
    D.complex hp2 φ (-τ)

end NLS.ZakharovShabat.SourceSection20Data
