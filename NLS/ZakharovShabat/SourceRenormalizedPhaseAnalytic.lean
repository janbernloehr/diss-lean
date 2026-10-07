import NLS.Dynamics.AnalyticComplexPhaseTrajectory
import NLS.ZakharovShabat.SourceRenormalizedFlowTrajectories
import NLS.ZakharovShabat.SourceFrequencySequenceAnalytic
import NLS.SequenceSpaces.ExponentEmbedding

/-! # Analytic dependence of compact-time renormalized coordinate trajectories

The actual moment-sum frequency sequence is analytic into ell^p and hence
into bounded sequences. Its Banach-algebra exponential supplies a complex
analytic extension of the real coordinate trajectories, in the uniform
norm on each compact time interval. This proves analytic dependence in
that trajectory space, rather than merely at individual modes or times.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual frequency correction as a bounded symbol on its analytic domain. -/
def boundedPhaseCorrection (A : SourceAbelianMomentAtlas hp hp1 W s)
    (φ : CoeffPair p) : Coeff ⊤ :=
  Coeff.exponentInclusion le_top (A.frequencySequence p φ)

/-- One complex neighborhood controls the bounded correction and all its coordinates. -/
theorem exists_analytic_boundedPhaseCorrection (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ A.domain ∩ P ∧
      AnalyticOnNhd ℂ A.boundedPhaseCorrection U ∧
      ∀ φ ∈ U, ∀ n, A.boundedPhaseCorrection φ n = A.renormalizedFrequency n φ := by
  obtain ⟨U,hU,_,hrU,hUP,ha,_⟩ := A.exists_analytic_frequencySequence hs hP hr
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨he,ha⟩ := ha p hp hp1 hhalf
  refine ⟨U,hU,hrU,hUP,?_,he⟩
  intro φ hφ
  exact ((Coeff.exponentInclusion (show p ≤ ⊤ from le_top)).analyticAt _).comp (ha φ hφ)

/-- Complex extension of the actual coordinate trajectory on [-T,T]. -/
def complexPhaseTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (T : ℝ) (φ : CoeffPair p) :
    C(Icc (-T) T, Coeff p × Coeff p) :=
  Birkhoff.analyticPhaseTrajectory hp (fun n : ℤ => (2*Real.pi*n)^2)
    ⟨Subtype.val,continuous_subtype_val⟩ (A.boundedPhaseCorrection φ)
    (sourceComplexBirkhoffMap hp hp1 t φ)

/-- All compact-time trajectory maps are complex analytic on one common source neighborhood. -/
theorem exists_analytic_complexPhaseTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧
      (∀ T : ℝ, AnalyticOnNhd ℂ (A.complexPhaseTrajectoryOn t T) U) ∧
      ∀ T : ℝ, ∀ φ : realTypeSourceSubmodule p,
        A.complexPhaseTrajectoryOn t T φ.val = A.renormalizedPhaseTrajectoryOn hs hP hr D T φ := by
  obtain ⟨V,hV,hrV,_,ha,he⟩ := A.exists_analytic_boundedPhaseCorrection hs hP hr
  refine ⟨V ∩ X,hV.inter D.source_open,fun φ hφ => ⟨hrV hφ,D.real_subset hφ⟩,?_,?_⟩
  · intro T φ hφ
    simpa only [complexPhaseTrajectoryOn, Function.comp_def] using!
      (Birkhoff.analyticAt_analyticPhaseTrajectory hp (fun n : ℤ => (2*Real.pi*n)^2)
        (⟨Subtype.val,continuous_subtype_val⟩ : C(Icc (-T) T, ℝ))
        (A.boundedPhaseCorrection φ,sourceComplexBirkhoffMap hp hp1 t φ)).comp
        (f := fun ψ => (A.boundedPhaseCorrection ψ,sourceComplexBirkhoffMap hp hp1 t ψ))
        ((ha φ hφ.1).prod (D.complex_map_analytic φ hφ.2))
  · intro T φ
    apply ContinuousMap.ext
    intro τ
    apply Prod.ext <;> ext n
    · rw [complexPhaseTrajectoryOn, Birkhoff.analyticPhaseTrajectory_fst,he φ.val (hrV φ.property)]
      change _ = (A.renormalizedPhaseTrajectory t φ τ.val).1 n
      rw [A.renormalizedPhaseTrajectory_fst hs.toSourcePsiIsolatingComplexExtension]
      push_cast
      rfl
    · rw [complexPhaseTrajectoryOn, Birkhoff.analyticPhaseTrajectory_snd,he φ.val (hrV φ.property)]
      change _ = (A.renormalizedPhaseTrajectory t φ τ.val).2 n
      rw [A.renormalizedPhaseTrajectory_snd hs.toSourcePsiIsolatingComplexExtension]
      push_cast
      rfl

/-- Real analytic dependence of the full compact-time coordinate trajectory on its initial source. -/
theorem analytic_renormalizedPhaseTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (T : ℝ) : AnalyticOnNhd ℝ (A.renormalizedPhaseTrajectoryOn hs hP hr D T) univ := by
  obtain ⟨U,_,hrU,ha,he⟩ := A.exists_analytic_complexPhaseTrajectoryOn hs hP hr D
  intro φ _
  have h := ((ha T φ.val (hrU φ.property)).restrictScalars (𝕜 := ℝ)).comp
    ((realTypeSourceSubmodule p).subtypeL.analyticAt (𝕜 := ℝ) (x := φ))
  simpa only [Function.comp_def,he] using! h

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
