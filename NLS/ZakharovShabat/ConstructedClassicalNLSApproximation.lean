import NLS.ZakharovShabat.SmoothNLSData
import NLS.ZakharovShabat.ClassicalNLSSmoothApproximationExponent

/-! # Approximation by the constructed solutions of arbitrary smooth data

Only smooth initial data and their source-norm convergence are supplied.
The global classical trajectories are constructed, with each renormalized
solution using its own initial physical mass.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P V B X : Set (CoeffPair p)}
variable {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Arbitrary smooth ordinary solutions converge uniformly on compact time intervals. -/
theorem tendstoUniformlyOn_constructedOrdinarySource
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) {ι : Type*} {l : Filter ι} (f : ι → SmoothNLSData)
    (φ : realTypeSourceSubmodule p)
    (hinit : Tendsto (fun j => (f j).source p) l (𝓝 φ)) (T : ℝ) :
    TendstoUniformlyOn (fun j => (f j).ordinarySource p)
      (A.hamiltonianOrdinarySourceFlow D hp2 φ) l (Icc (-T) T) := by
  apply A.tendstoUniformlyOn_classicalNLSSource_of_smoothInitial hs hP hr D hp2
    (fun j => (f j).ordinary) (fun j => (f j).ordinary_isClassical) φ
  change Tendsto (fun j => (f j).ordinarySource p 0) l (𝓝 φ)
  simpa only [SmoothNLSData.ordinarySource_zero] using hinit

/-- Arbitrary smooth renormalized solutions converge uniformly in the global exponent range. -/
theorem tendstoUniformlyOn_constructedRenormalizedSource
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) {ι : Type*} {l : Filter ι} (f : ι → SmoothNLSData)
    (φ : realTypeSourceSubmodule p)
    (hinit : Tendsto (fun j => (f j).source p) l (𝓝 φ)) (T : ℝ) :
    TendstoUniformlyOn (fun j => (f j).renormalizedSource p)
      (A.hamiltonianRenormalizedSourceFlow D hp2 φ) l (Icc (-T) T) := by
  apply A.tendstoUniformlyOn_classicalRenormalizedNLSSource_of_smoothInitial hs hP hr D hp2
    (fun j => (f j).renormalized) (fun j => (f j).renormalized_isClassical) φ
  change Tendsto (fun j => (f j).renormalizedSource p 0) l (𝓝 φ)
  simpa only [SmoothNLSData.renormalizedSource_zero] using hinit

/-- At higher exponents, arbitrary smooth solutions converge on every admissible compact interval. -/
theorem tendstoUniformlyOn_constructedRenormalizedImageSource
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (h2p : 2 ≤ p) {ι : Type*} {l : Filter ι} (f : ι → SmoothNLSData)
    (φ : realTypeSourceSubmodule p)
    (hinit : Tendsto (fun j => (f j).source p) l (𝓝 φ)) (T : ℝ)
    (hφ : φ ∈ A.renormalizedTrajectoryDomain t T) :
    TendstoUniformlyOn (fun j => (f j).renormalizedSource p)
      (A.hamiltonianRenormalizedImageFlow D φ) l (Icc (-T) T) := by
  apply A.tendstoUniformlyOn_classicalRenormalizedImageSource_of_smoothInitial hs hP hr D h2p
    (fun j => (f j).renormalized) (fun j => (f j).renormalized_isClassical) φ _ T hφ
  change Tendsto (fun j => (f j).renormalizedSource p 0) l (𝓝 φ)
  simpa only [SmoothNLSData.renormalizedSource_zero] using hinit

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
