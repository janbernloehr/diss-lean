import NLS.ZakharovShabat.SourceBirkhoffImageInverse

/-! # Renormalized flow while its coordinates remain in the Birkhoff image

The inverse on the actual open coordinate image gives the source flow at
every finite exponent above one. The image condition is explicit. The
coordinate identity, actions, frequencies and group law are proved on
that domain, without assuming global surjectivity.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Times and initial sources for which the actual coordinate inverse is available. -/
def renormalizedImageDomain (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Set (ℝ × realTypeSourceSubmodule p) :=
  {x | Birkhoff.decodeReal (A.renormalizedPhaseTrajectory t x.2 x.1) ∈
    range (sourceRealBirkhoffMap hp hp1 t)}

/-- Equation (4.15) on the actual image; regularity and flow identities use the domain guard. -/
def renormalizedImageFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) : realTypeSourceSubmodule p :=
  D.realImageInverse (Birkhoff.decodeReal (A.renormalizedPhaseTrajectory t φ τ))

/-- Every initial source is admissible at time zero. -/
theorem zero_mem_renormalizedImageDomain (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p) :
    (0,φ) ∈ A.renormalizedImageDomain t := by
  change Birkhoff.decodeReal (A.renormalizedPhaseTrajectory t φ 0) ∈
    range (sourceRealBirkhoffMap hp hp1 t)
  rw [A.renormalizedPhaseTrajectory_zero,← D.encode_real_map,Birkhoff.decodeReal_encodeReal]
  exact mem_range_self φ

/-- The original source flow has exactly the intended phase coordinates whenever admissible. -/
theorem complex_map_renormalizedImageFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p) (τ : ℝ)
    (h : (τ,φ) ∈ A.renormalizedImageDomain t) :
    sourceComplexBirkhoffMap hp hp1 t (A.renormalizedImageFlow D φ τ).val =
      A.renormalizedPhaseTrajectory t φ τ := by
  rw [← D.encode_real_map]
  change Birkhoff.encodeReal (sourceRealBirkhoffMap hp hp1 t
    (D.realImageInverse (Birkhoff.decodeReal (A.renormalizedPhaseTrajectory t φ τ)))) = _
  rw [D.real_map_realImageInverse _ h]
  exact Birkhoff.encodeReal_decodeReal _ (A.renormalizedPhaseTrajectory_real D φ τ)

@[simp] theorem renormalizedImageFlow_zero (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p) :
    A.renormalizedImageFlow D φ 0 = φ := by
  apply D.complex_map_real_injective
  dsimp only
  rw [A.complex_map_renormalizedImageFlow D φ 0 (A.zero_mem_renormalizedImageDomain D φ),
    A.renormalizedPhaseTrajectory_zero]

/-- The domain is open jointly in time and initial source. -/
theorem isOpen_renormalizedImageDomain (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    IsOpen (A.renormalizedImageDomain t) :=
  D.real_image_open.preimage (Birkhoff.decodeReal.continuous.comp
    (A.continuous_renormalizedPhaseTrajectory hs hP hr D))

/-- Joint source-flow continuity on its open image domain. -/
theorem continuousOn_renormalizedImageFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    ContinuousOn (fun x : ℝ × realTypeSourceSubmodule p => A.renormalizedImageFlow D x.2 x.1)
      (A.renormalizedImageDomain t) :=
  D.realImageInverse_analytic.continuousOn.comp
    (Birkhoff.decodeReal.continuous.comp (A.continuous_renormalizedPhaseTrajectory hs hP hr D)).continuousOn
    (fun _ h => h)

/-- Every original spectral action is preserved wherever the source flow is defined. -/
theorem renormalizedImageFlow_action (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p) (τ : ℝ)
    (h : (τ,φ) ∈ A.renormalizedImageDomain t) (n : ℤ) :
    sourceComplexAction hp hp1 n (A.renormalizedImageFlow D φ τ).val =
      sourceComplexAction hp hp1 n φ.val := by
  rw [← D.complex_map_action _ (D.real_subset (A.renormalizedImageFlow D φ τ).property) n,
    A.complex_map_renormalizedImageFlow D φ τ h]
  exact A.renormalizedPhaseTrajectory_action D φ τ n

/-- The actual renormalized frequencies stay constant along admissible trajectories. -/
theorem phaseFrequency_renormalizedImageFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p) (τ : ℝ)
    (h : (τ,φ) ∈ A.renormalizedImageDomain t) :
    A.phaseFrequency (A.renormalizedImageFlow D φ τ) = A.phaseFrequency φ := by
  have hlevel : A.renormalizedImageFlow D φ τ ∈ sourceRealActionLevelSet hp hp1 φ := by
    intro n
    have he := A.renormalizedImageFlow_action D φ τ h n
    rw [sourceComplexAction_eq_sourceRealAction hp hp1 n _ (A.renormalizedImageFlow D φ τ).property,
      sourceComplexAction_eq_sourceRealAction hp hp1 n _ φ.property] at he
    exact congrArg Complex.re he
  funext n
  rw [phaseFrequency,phaseFrequency,A.renormalizedFrequency_real_eq_of_actions A hs hs φ
    (A.renormalizedImageFlow D φ τ) hlevel n]

/-- Restarting an admissible trajectory adds its phase times. -/
theorem phaseTrajectory_renormalizedImageFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p) (τ σ : ℝ)
    (hσ : (σ,φ) ∈ A.renormalizedImageDomain t) :
    A.renormalizedPhaseTrajectory t (A.renormalizedImageFlow D φ σ) τ =
      A.renormalizedPhaseTrajectory t φ (τ+σ) := by
  simp only [renormalizedPhaseTrajectory,A.phaseFrequency_renormalizedImageFlow hs D φ σ hσ,
    A.complex_map_renormalizedImageFlow D φ σ hσ]
  exact Birkhoff.phaseFlow_add _ τ σ _

/-- The admissible times transform correctly under restarting the nonlinear flow. -/
theorem mem_imageDomain_restart_iff (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p) (τ σ : ℝ)
    (hσ : (σ,φ) ∈ A.renormalizedImageDomain t) :
    (τ,A.renormalizedImageFlow D φ σ) ∈ A.renormalizedImageDomain t ↔
      (τ+σ,φ) ∈ A.renormalizedImageDomain t := by
  change Birkhoff.decodeReal (A.renormalizedPhaseTrajectory t (A.renormalizedImageFlow D φ σ) τ) ∈
    range (sourceRealBirkhoffMap hp hp1 t) ↔
    Birkhoff.decodeReal (A.renormalizedPhaseTrajectory t φ (τ+σ)) ∈
    range (sourceRealBirkhoffMap hp hp1 t)
  rw [A.phaseTrajectory_renormalizedImageFlow hs D φ τ σ hσ]

/-- Time addition for the source flow, with its initial admissibility stated explicitly. -/
theorem renormalizedImageFlow_add (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (φ : realTypeSourceSubmodule p) (τ σ : ℝ)
    (hσ : (σ,φ) ∈ A.renormalizedImageDomain t) :
    A.renormalizedImageFlow D (A.renormalizedImageFlow D φ σ) τ =
      A.renormalizedImageFlow D φ (τ+σ) := by
  change D.realImageInverse (Birkhoff.decodeReal
    (A.renormalizedPhaseTrajectory t (A.renormalizedImageFlow D φ σ) τ)) = _
  rw [A.phaseTrajectory_renormalizedImageFlow hs D φ τ σ hσ]
  rfl

/-- In the globally surjective range this is exactly the previously constructed global flow. -/
theorem renormalizedImageFlow_eq_global (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    A.renormalizedImageFlow D φ τ = A.renormalizedSourceFlow D hp2 φ τ := by
  apply D.complex_map_real_injective
  dsimp only
  rw [A.complex_map_renormalizedSourceFlow]
  exact A.complex_map_renormalizedImageFlow D φ τ (D.proposition17_3 hp2 _)

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
