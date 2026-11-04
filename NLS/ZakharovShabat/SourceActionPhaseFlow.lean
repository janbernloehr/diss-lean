import NLS.ZakharovShabat.SourceBirkhoffImageInverse
import NLS.Dynamics.HamiltonianPhaseFlow

/-! # Action-invariant Hamiltonian phase flows in the actual open Birkhoff image

The real frequency family is arbitrary but continuous coordinatewise and
constant on original spectral action levels. The Hamiltonian phase has the
negative sign in the first component. Every inverse identity carries its
actual image condition; no global surjectivity is required.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}

/-- Verified data for a real action-invariant spectral frequency family. -/
structure SourceActionFrequency (hp : p ≠ ⊤) (hp1 : 1 < p) where
  frequency : realTypeSourceSubmodule p → ℤ → ℝ
  continuous : ∀ n, Continuous (fun φ => frequency φ n)
  invariant : ∀ φ ψ : realTypeSourceSubmodule p,
    ψ ∈ sourceRealActionLevelSet hp hp1 φ → frequency ψ = frequency φ

namespace SourceActionFrequency
variable {W₀ B X : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The exact Hamiltonian coordinate trajectory, before source inversion. -/
def phaseTrajectory (F : SourceActionFrequency hp hp1)
    (_D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) : Coeff p × Coeff p :=
  Birkhoff.hamiltonianPhaseFlow (F.frequency φ) τ (sourceComplexBirkhoffMap hp hp1 s φ.val)

@[simp] theorem phaseTrajectory_zero (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) :
    F.phaseTrajectory D φ 0 = sourceComplexBirkhoffMap hp hp1 s φ.val :=
  Birkhoff.hamiltonianPhaseFlow_zero _ _

/-- The opposite phases preserve the original spectral action at every index. -/
theorem phaseTrajectory_action (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    (F.phaseTrajectory D φ τ).1 n*(F.phaseTrajectory D φ τ).2 n = sourceComplexAction hp hp1 n φ.val :=
  (Birkhoff.phaseFlow_action _ _ _ _).trans (D.complex_map_action φ.val (D.real_subset φ.property) n)

/-- The trajectory stays in the actual conjugate-pair real form. -/
theorem phaseTrajectory_real (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) : Birkhoff.IsConjugatePair (F.phaseTrajectory D φ τ) :=
  Birkhoff.phaseFlow_real _ _ _ (D.complex_map_real φ)

/-- The complete coordinate norm is preserved for every real time. -/
theorem phaseTrajectory_norm (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    ‖F.phaseTrajectory D φ τ‖ = ‖sourceComplexBirkhoffMap hp hp1 s φ.val‖ :=
  Birkhoff.norm_phaseFlow _ _ _

/-- Joint continuity requires only coordinatewise frequency continuity. -/
theorem continuous_phaseTrajectory (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) :
    Continuous (fun x : ℝ × realTypeSourceSubmodule p => F.phaseTrajectory D x.2 x.1) := by
  have h := Birkhoff.continuous_phaseFlow_family hp F.frequency
    (fun φ => sourceComplexBirkhoffMap hp hp1 s φ.val) F.continuous D.continuous_complex_map_real
  exact h.comp (continuous_fst.neg.prodMk continuous_snd)

/-- The exact set of time-source pairs for which the coordinate inverse is available. -/
def imageDomain (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) : Set (ℝ × realTypeSourceSubmodule p) :=
  {x | Birkhoff.decodeReal (F.phaseTrajectory D x.2 x.1) ∈ range (sourceRealBirkhoffMap hp hp1 s)}

/-- Lift the phase curve by the actual inverse on its open image. -/
def imageFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    realTypeSourceSubmodule p := D.realImageInverse (Birkhoff.decodeReal (F.phaseTrajectory D φ τ))

@[simp] theorem zero_mem_imageDomain (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) :
    (0,φ) ∈ F.imageDomain D := by
  change Birkhoff.decodeReal (F.phaseTrajectory D φ 0) ∈ range (sourceRealBirkhoffMap hp hp1 s)
  rw [F.phaseTrajectory_zero,← D.encode_real_map,Birkhoff.decodeReal_encodeReal]
  exact mem_range_self φ

/-- The source lift has exactly the specified coordinates whenever admissible. -/
theorem complex_map_imageFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) (τ : ℝ)
    (h : (τ,φ) ∈ F.imageDomain D) :
    sourceComplexBirkhoffMap hp hp1 s (F.imageFlow D φ τ).val = F.phaseTrajectory D φ τ := by
  rw [← D.encode_real_map]
  change Birkhoff.encodeReal (sourceRealBirkhoffMap hp hp1 s
    (D.realImageInverse (Birkhoff.decodeReal (F.phaseTrajectory D φ τ)))) = _
  rw [D.real_map_realImageInverse _ h]
  exact Birkhoff.encodeReal_decodeReal _ (F.phaseTrajectory_real D φ τ)

@[simp] theorem imageFlow_zero (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) :
    F.imageFlow D φ 0 = φ := by
  apply D.complex_map_real_injective
  dsimp only
  rw [F.complex_map_imageFlow D φ 0 (F.zero_mem_imageDomain D φ),F.phaseTrajectory_zero]

/-- The admissible time-source domain is open in the original norm. -/
theorem isOpen_imageDomain (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) : IsOpen (F.imageDomain D) :=
  D.real_image_open.preimage (Birkhoff.decodeReal.continuous.comp (F.continuous_phaseTrajectory D))

/-- The actual source lift is jointly continuous on its admissible domain. -/
theorem continuousOn_imageFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) :
    ContinuousOn (fun x : ℝ × realTypeSourceSubmodule p => F.imageFlow D x.2 x.1) (F.imageDomain D) :=
  D.realImageInverse_analytic.continuousOn.comp
    (Birkhoff.decodeReal.continuous.comp (F.continuous_phaseTrajectory D)).continuousOn (fun _ h => h)

/-- The source flow preserves every original action, including closed ones. -/
theorem imageFlow_action (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) (τ : ℝ)
    (h : (τ,φ) ∈ F.imageDomain D) (n : ℤ) :
    sourceComplexAction hp hp1 n (F.imageFlow D φ τ).val = sourceComplexAction hp hp1 n φ.val := by
  rw [← D.complex_map_action _ (D.real_subset (F.imageFlow D φ τ).property) n,F.complex_map_imageFlow D φ τ h]
  exact F.phaseTrajectory_action D φ τ n

/-- Frequency invariance uses actual spectral action preservation. -/
theorem frequency_imageFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) (τ : ℝ)
    (h : (τ,φ) ∈ F.imageDomain D) : F.frequency (F.imageFlow D φ τ) = F.frequency φ := by
  apply F.invariant
  intro n
  have he := F.imageFlow_action D φ τ h n
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n _ (F.imageFlow D φ τ).property,
    sourceComplexAction_eq_sourceRealAction hp hp1 n _ φ.property] at he
  exact congrArg Complex.re he

/-- Restarting an admissible trajectory adds the original physical time parameters. -/
theorem phaseTrajectory_imageFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) (τ σ : ℝ)
    (hσ : (σ,φ) ∈ F.imageDomain D) :
    F.phaseTrajectory D (F.imageFlow D φ σ) τ = F.phaseTrajectory D φ (τ+σ) := by
  simp only [phaseTrajectory,F.frequency_imageFlow D φ σ hσ,F.complex_map_imageFlow D φ σ hσ]
  exact Birkhoff.hamiltonianPhaseFlow_add _ τ σ _

/-- The open image condition transforms exactly under restarting. -/
theorem mem_imageDomain_restart_iff (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) (τ σ : ℝ)
    (hσ : (σ,φ) ∈ F.imageDomain D) :
    (τ,F.imageFlow D φ σ) ∈ F.imageDomain D ↔ (τ+σ,φ) ∈ F.imageDomain D := by
  change Birkhoff.decodeReal (F.phaseTrajectory D (F.imageFlow D φ σ) τ) ∈ range (sourceRealBirkhoffMap hp hp1 s) ↔
    Birkhoff.decodeReal (F.phaseTrajectory D φ (τ+σ)) ∈ range (sourceRealBirkhoffMap hp hp1 s)
  rw [F.phaseTrajectory_imageFlow D φ τ σ hσ]

/-- The lifted nonlinear flow has the time-addition law on its actual domain. -/
theorem imageFlow_add (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) (τ σ : ℝ)
    (hσ : (σ,φ) ∈ F.imageDomain D) :
    F.imageFlow D (F.imageFlow D φ σ) τ = F.imageFlow D φ (τ+σ) := by
  change D.realImageInverse (Birkhoff.decodeReal (F.phaseTrajectory D (F.imageFlow D φ σ) τ)) = _
  rw [F.phaseTrajectory_imageFlow D φ τ σ hσ]
  rfl

/-- Every admissible forward step has an admissible inverse step. -/
theorem neg_mem_imageDomain (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) (τ : ℝ)
    (h : (τ,φ) ∈ F.imageDomain D) : (-τ,F.imageFlow D φ τ) ∈ F.imageDomain D := by
  rw [F.mem_imageDomain_restart_iff D φ (-τ) τ h,neg_add_cancel]
  exact F.zero_mem_imageDomain D φ

/-- Negative time reverses every admissible physical time step. -/
theorem imageFlow_neg (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (φ : realTypeSourceSubmodule p) (τ : ℝ)
    (h : (τ,φ) ∈ F.imageDomain D) : F.imageFlow D (F.imageFlow D φ τ) (-τ) = φ := by
  rw [F.imageFlow_add D φ (-τ) τ h,neg_add_cancel,F.imageFlow_zero]

end SourceActionFrequency
end NLS.ZakharovShabat
