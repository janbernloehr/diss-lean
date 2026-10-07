import NLS.ZakharovShabat.SmoothClassicalNLSAgreement

/-! # Convergence for arbitrary smooth classical approximations in the Hilbert source

Every family of classical ordinary or renormalized solutions whose actual
initial Fourier sources converge in the Hilbert norm converges uniformly
on compact time intervals in physical L² to the corresponding spectral
trajectory. No finite-gap, H¹ convergence, or uniform amplitude hypothesis
is imposed on the approximation family.
-/
noncomputable section
open Set Filter Topology MeasureTheory NLS.Fourier
namespace NLS.ZakharovShabat

/-- Continuous physical realization of an original Hilbert source. -/
def sourceFirstPeriodOneL2Map :
    C(realTypeSourceSubmodule 2,Lp ℂ 2 (AddCircle.haarAddCircle (T := (2 : ℝ)))) :=
  ⟨sourceFirstPeriodOneL2,continuous_sourceFirstPeriodOneL2⟩

/-- The literal physical L² path of a continuous classical trajectory. -/
def classicalPhysicalL2Path (T : ℝ) (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) (hu : Continuous u) :
    C(Icc (-T) T,Lp ℂ 2 (AddCircle.haarAddCircle (T := (2 : ℝ)))) :=
  ⟨fun time => ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u time.val),
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).continuous.comp (hu.comp continuous_subtype_val)⟩

namespace SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Arbitrary smooth ordinary approximations converge in the uniform compact-time
physical L² norm whenever their initial Hilbert sources converge. -/
theorem tendsto_classicalNLSPhysicalPath_of_smoothInitial
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P s)
    (hP : IsOpen P) (hr : realTypeSourceLocus 2 ⊆ P)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    {ι : Type*} {l : Filter ι} (u : ι → ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : ∀ j, IsClassicalNLSTrajectory (u j)) (φ : realTypeSourceSubmodule 2)
    (hinit : Tendsto (fun j => smoothPeriodOneHilbertSource (u j 0)
      ((hu j).spatial_smooth 0) ((hu j).periodic 0)) l (𝓝 φ)) (T : ℝ) :
    Tendsto (fun j => classicalPhysicalL2Path T (u j) (hu j).time_differentiable.continuous) l
      (𝓝 (sourceFirstPeriodOneL2Map.comp (A.hamiltonianOrdinarySourceTrajectoryOn hs hP hr D le_rfl T φ))) := by
  have hsource := A.tendsto_hamiltonianOrdinarySourceTrajectoryOn hs hP hr D le_rfl T φ _ hinit
  have hlim := sourceFirstPeriodOneL2Map.continuous_postcomp.continuousAt.tendsto.comp hsource
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro j
  apply ContinuousMap.ext
  intro time
  exact (A.classicalNLS_toLp_eq_hamiltonianFlow hs hP hr D
    (smoothPeriodOneSource (u j 0) ((hu j).spatial_smooth 0) ((hu j).periodic 0)) (u j) (hu j)
    (periodOneSobolevSynthesis_smoothPeriodOneSource _ _ _).symm time.val).symm

/-- Every smooth renormalized approximation has the same compact-time limit.
Each member uses its own physical initial mass; masses need not coincide. -/
theorem tendsto_classicalRenormalizedNLSPhysicalPath_of_smoothInitial
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P s)
    (hP : IsOpen P) (hr : realTypeSourceLocus 2 ⊆ P)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    {ι : Type*} {l : Filter ι} (u : ι → ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : ∀ j, IsClassicalRenormalizedNLSTrajectory (classicalNLSMass (u j 0)) (u j))
    (φ : realTypeSourceSubmodule 2)
    (hinit : Tendsto (fun j => smoothPeriodOneHilbertSource (u j 0)
      ((hu j).spatial_smooth 0) ((hu j).periodic 0)) l (𝓝 φ)) (T : ℝ) :
    Tendsto (fun j => classicalPhysicalL2Path T (u j) (hu j).time_differentiable.continuous) l
      (𝓝 (sourceFirstPeriodOneL2Map.comp (A.hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D le_rfl T φ))) := by
  have hsource := A.tendsto_hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D le_rfl T φ _ hinit
  have hlim := sourceFirstPeriodOneL2Map.continuous_postcomp.continuousAt.tendsto.comp hsource
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro j
  apply ContinuousMap.ext
  intro time
  exact (A.classicalRenormalizedNLS_toLp_eq_hamiltonianFlow hs hP hr D
    (smoothPeriodOneSource (u j 0) ((hu j).spatial_smooth 0) ((hu j).periodic 0)) (u j) (hu j)
    (periodOneSobolevSynthesis_smoothPeriodOneSource _ _ _).symm time.val).symm

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
