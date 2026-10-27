import NLS.ZakharovShabat.SourceSobolevAnalyticPhaseLift
import NLS.ZakharovShabat.SourceSobolevAlmostPeriodic
import NLS.ZakharovShabat.SourceOrdinaryPhaseAnalytic

/-! # Analytic dependence of the original NLS solutions in every Sobolev norm -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P W₀ B X : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {K : Type} [TopologicalSpace K] [CompactSpace K]

/-- Both actual Hamiltonian flows admit real analytic trajectory maps in the
native Sobolev uniform norm, at every real nonnegative regularity. Forgetting
the weight gives the already constructed original source flows at every time. -/
theorem exists_analytic_sobolevHamiltonianTrajectories
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) (θ : C(K, ℝ)) :
    ∃ S Sstar : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ) →
      C(K, weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)),
      AnalyticOnNhd ℝ S univ ∧ AnalyticOnNhd ℝ Sstar univ ∧
      ∀ a k,
        originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (S a k) =
          A.hamiltonianOrdinarySourceFlow D hp2 (originalWeightedRealSource _ a) (θ k) ∧
        originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (Sstar a k) =
          A.hamiltonianRenormalizedSourceFlow D hp2 (originalWeightedRealSource _ a) (θ k) := by
  let w := sourceSobolevSpectralWeight σ hσ
  let J := ((originalWeightedSourceCLM (p := p) w).restrictScalars ℝ).comp
    (weightedRealSourceSubmodule (p := p) w).subtypeL
  let b := fun a : weightedRealSourceSubmodule (p := p) w => A.ordinaryBoundedCorrection hp2 (J a)
  let bstar := fun a : weightedRealSourceSubmodule (p := p) w => A.boundedPhaseCorrection (J a)
  obtain ⟨U,_,hrU,_,ha,he⟩ := A.exists_analytic_boundedPhaseCorrection hs hP hr
  have hJ (a : weightedRealSourceSubmodule (p := p) w) : J a ∈ U :=
    hrU (originalWeightedRealSource w a).property
  have hbstar : AnalyticOnNhd ℝ bstar univ := by
    intro a _
    exact ((ha (J a) (hJ a)).restrictScalars (𝕜 := ℝ)).comp (J.analyticAt a)
  have hb : AnalyticOnNhd ℝ b univ := by
    intro a _
    have hmass := ((analytic_sourceOrdinaryComplexMass hp2 (J a) (mem_univ _)).restrictScalars (𝕜 := ℝ)).comp (J.analyticAt a)
    exact (hbstar a (mem_univ _)).add ((analyticAt_const.mul hmass).smul analyticAt_const)
  let ω : ℤ → ℝ := fun n => (2*Real.pi*n)^2
  let S := D.correctedSobolevTrajectory hp2 σ hσ ω θ b
  let Sstar := D.correctedSobolevTrajectory hp2 σ hσ ω θ bstar
  refine ⟨S,Sstar,D.analytic_correctedSobolevTrajectory hp2 σ hσ ω θ b hb,
    D.analytic_correctedSobolevTrajectory hp2 σ hσ ω θ bstar hbstar,?_⟩
  intro a k
  let φ := originalWeightedRealSource w a
  have hsval (n : ℤ) : bstar a n = ((A.phaseFrequency φ n-ω n : ℝ) : ℂ) := by
    change A.boundedPhaseCorrection φ.val n = _
    rw [he φ.val (hJ a) n,Complex.ofReal_sub]
    have h := A.phaseFrequency_complex hs.toSourcePsiIsolatingComplexExtension φ n
    dsimp only [ω]
    push_cast
    linear_combination -h
  have hval (n : ℤ) : b a n = ((A.ordinaryPhaseFrequency hp2 φ n-ω n : ℝ) : ℂ) := by
    change A.boundedPhaseCorrection φ.val n+(4*sourceOrdinaryComplexMass hp2 φ.val)*1 = _
    rw [he φ.val (hJ a) n,mul_one,Complex.ofReal_sub]
    have h := A.ordinaryPhaseFrequency_complex hs.toSourcePsiIsolatingComplexExtension hp2 φ n
    dsimp only [ω]
    push_cast
    linear_combination -h
  have hω (f : ℤ → ℝ) : (fun n => ω n+(f n-ω n)) = f := by funext n; ring
  constructor
  · change originalWeightedRealSource w (D.correctedSobolevTrajectory hp2 σ hσ ω θ b a k) = _
    rw [D.correctedSobolevTrajectory_apply hp2 σ hσ ω θ b a _ hval k,hω]
    exact A.originalWeightedRealSource_ordinarySobolevPhase D hp2 σ hσ a (θ k)
  · change originalWeightedRealSource w (D.correctedSobolevTrajectory hp2 σ hσ ω θ bstar a k) = _
    rw [D.correctedSobolevTrajectory_apply hp2 σ hσ ω θ bstar a _ hsval k,hω]
    exact A.originalWeightedRealSource_renormalizedSobolevPhase D hp2 σ hσ a (θ k)

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
