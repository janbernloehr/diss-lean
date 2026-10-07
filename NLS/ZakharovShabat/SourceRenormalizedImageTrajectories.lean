import NLS.ZakharovShabat.SourceRenormalizedLocalFlow
import NLS.ZakharovShabat.SourceRenormalizedSourceTrajectoryAnalytic

/-! # Analytic local and small-data source trajectories

The admissible initial sources for a compact time interval form an open
set. On it the complete source trajectory is continuous and real analytic
in the uniform source norm. No global surjectivity assumption is needed.
-/
noncomputable section
open Set Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Initial sources admissible throughout the given compact time interval. -/
def renormalizedTrajectoryDomain (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (T : ℝ) : Set (realTypeSourceSubmodule p) :=
  {φ | ∀ τ : Icc (-T) T, (τ.val,φ) ∈ A.renormalizedImageDomain t}

/-- The compact-time source trajectory, with a harmless fallback off its asserted domain. -/
def renormalizedImageTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ)
    (φ : realTypeSourceSubmodule p) : C(Icc (-T) T,realTypeSourceSubmodule p) :=
  ContinuousMap.mkD (fun τ => A.renormalizedImageFlow D φ τ.val) 0

/-- Admissibility throughout a compact time interval is open in the initial source. -/
theorem isOpen_renormalizedTrajectoryDomain (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ) :
    IsOpen (A.renormalizedTrajectoryDomain t T) := by
  let G : realTypeSourceSubmodule p → C(Icc (-T) T,RealCoeff p × RealCoeff p) :=
    fun φ => (Birkhoff.decodeReal.compLeftContinuous ℝ (Icc (-T) T))
      (A.renormalizedPhaseTrajectoryOn hs hP hr D T φ)
  have hG : Continuous G := (Birkhoff.decodeReal.compLeftContinuous ℝ (Icc (-T) T)).continuous.comp
    (A.continuous_renormalizedPhaseTrajectoryOn hs hP hr D T)
  have he : A.renormalizedTrajectoryDomain t T =
      G ⁻¹' {g | range g ⊆ range (sourceRealBirkhoffMap hp hp1 t)} := by
    ext φ
    exact ⟨fun h _ ⟨τ,hτ⟩ => hτ ▸ h τ,fun h τ => h ⟨τ,rfl⟩⟩
  rw [he]
  exact (ContinuousMap.isOpen_setOfPred_range_subset D.real_image_open).preimage hG

/-- The path is continuous in time whenever all its times are admissible. -/
theorem continuous_renormalizedImagePath (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (T : ℝ) (φ : realTypeSourceSubmodule p) (hφ : φ ∈ A.renormalizedTrajectoryDomain t T) :
    Continuous (fun τ : Icc (-T) T => A.renormalizedImageFlow D φ τ.val) := by
  exact (A.continuousOn_renormalizedImageFlow hs hP hr D).comp_continuous
    (f := fun τ : Icc (-T) T => (τ.val,φ))
    (continuous_subtype_val.prodMk continuous_const) hφ

/-- Evaluation gives the actual source flow at every admissible time. -/
theorem renormalizedImageTrajectoryOn_apply (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (T : ℝ) (φ : realTypeSourceSubmodule p) (hφ : φ ∈ A.renormalizedTrajectoryDomain t T)
    (τ : Icc (-T) T) :
    A.renormalizedImageTrajectoryOn D T φ τ = A.renormalizedImageFlow D φ τ.val :=
  ContinuousMap.mkD_apply_of_continuous (A.continuous_renormalizedImagePath hs hP hr D T φ hφ)

/-- Continuity in the uniform source trajectory norm on the open initial-data domain. -/
theorem continuousOn_renormalizedImageTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ) :
    ContinuousOn (A.renormalizedImageTrajectoryOn D T) (A.renormalizedTrajectoryDomain t T) := by
  apply ContinuousMap.continuousOn_mkD_of_uncurry
  exact (A.continuousOn_renormalizedImageFlow hs hP hr D).comp
    (f := fun x : realTypeSourceSubmodule p × Icc (-T) T => (x.2.val,x.1))
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst).continuousOn
    (fun x hx => hx.1 x.2)

/-- The same source path with its closed real subtype forgotten. -/
def ambientImageTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ)
    (φ : realTypeSourceSubmodule p) : C(Icc (-T) T,CoeffPair p) :=
  ((realTypeSourceSubmodule p).subtypeL.compLeftContinuous ℝ (Icc (-T) T))
    (A.renormalizedImageTrajectoryOn D T φ)

/-- The actual Birkhoff image is the previously constructed analytic coordinate trajectory. -/
theorem superposition_ambientImageTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (T : ℝ) (φ : realTypeSourceSubmodule p) (hφ : φ ∈ A.renormalizedTrajectoryDomain t T) :
    superposition (sourceBirkhoffMap hp hp1 t) (A.ambientImageTrajectoryOn D T φ) =
      A.rectangularPhaseTrajectoryOn hs hP hr D T φ := by
  apply ContinuousMap.ext
  intro τ
  rw [superposition_apply D.analytic.continuousOn (by
    rintro _ ⟨σ,rfl⟩
    exact D.real_subset (A.renormalizedImageTrajectoryOn D T φ σ).property)]
  change sourceBirkhoffMap hp hp1 t (A.renormalizedImageTrajectoryOn D T φ τ).val =
    Birkhoff.rectangularToComplex.symm (A.renormalizedPhaseTrajectory t φ τ.val)
  rw [A.renormalizedImageTrajectoryOn_apply hs hP hr D T φ hφ τ]
  have h := congrArg (Birkhoff.rectangularToComplex (p := p)).symm
    (A.complex_map_renormalizedImageFlow D φ τ.val (hφ τ))
  simpa only [sourceComplexBirkhoffMap,ContinuousLinearEquiv.symm_apply_apply] using! h

/-- Analyticity of the full ambient source path on every admissible compact interval. -/
theorem analytic_ambientImageTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ) :
    AnalyticOnNhd ℝ (A.ambientImageTrajectoryOn D T) (A.renormalizedTrajectoryDomain t T) := by
  intro φ hφ
  have hopen := A.isOpen_renormalizedTrajectoryDomain hs hP hr D T
  apply analyticAt_real_lift_of_superposition D.source_open D.analytic
    (A.ambientImageTrajectoryOn D T) φ
  · exact ((realTypeSourceSubmodule p).subtypeL.compLeftContinuous ℝ (Icc (-T) T)).continuous.continuousAt.comp
      ((A.continuousOn_renormalizedImageTrajectoryOn hs hP hr D T φ hφ).continuousAt
        (hopen.mem_nhds hφ))
  · rintro _ ⟨τ,rfl⟩
    exact D.real_subset (A.renormalizedImageTrajectoryOn D T φ τ).property
  · intro τ
    exact ⟨D.jacobianEquivAll (A.renormalizedImageTrajectoryOn D T φ τ),rfl⟩
  · have hrect :=
      ((((Birkhoff.rectangularToComplex (p := p)).symm.toContinuousLinearMap.compLeftContinuous ℂ
        (Icc (-T) T)).restrictScalars ℝ).analyticAt _).comp
        (A.analytic_renormalizedPhaseTrajectoryOn hs hP hr D T φ (mem_univ _))
    have ha : AnalyticAt ℝ (A.rectangularPhaseTrajectoryOn hs hP hr D T) φ := hrect
    apply ha.congr
    filter_upwards [hopen.mem_nhds hφ] with ψ hψ
    exact (A.superposition_ambientImageTrajectoryOn hs hP hr D T ψ hψ).symm

/-- Analytic initial-data dependence in the full source trajectory norm, also for p > 2. -/
theorem analytic_renormalizedImageTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ) :
    AnalyticOnNhd ℝ (A.renormalizedImageTrajectoryOn D T) (A.renormalizedTrajectoryDomain t T) := by
  have he (φ : realTypeSourceSubmodule p) :
      ((sourceRealTypeProjection hp).compLeftContinuous ℝ (Icc (-T) T))
        (A.ambientImageTrajectoryOn D T φ) = A.renormalizedImageTrajectoryOn D T φ := by
    apply ContinuousMap.ext
    intro τ
    exact sourceRealTypeProjection_subtype hp (A.renormalizedImageTrajectoryOn D T φ τ)
  intro φ hφ
  have h := (((sourceRealTypeProjection hp).compLeftContinuous ℝ (Icc (-T) T)).analyticAt _).comp
    (A.analytic_ambientImageTrajectoryOn hs hP hr D T φ hφ)
  simpa only [Function.comp_def,he] using! h

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
