import NLS.ZakharovShabat.SourceRenormalizedPhaseTrajectory
import NLS.Dynamics.RealComplexBirkhoffCoordinates
import NLS.ZakharovShabat.SourceBirkhoffGlobalInverse
import NLS.ZakharovShabat.SourceFrequencyActionInvariance

/-! # The global continuous renormalized source flow for 1 < p ≤ 2

The actual global Birkhoff inverse lifts the complex phase trajectories.
Preservation of the original actions makes the actual frequencies constant
along each trajectory; this proves the nonlinear time-addition law.
The result is a continuous group of source homeomorphisms. Analyticity of
compact-time trajectory maps and agreement with classical NLS solutions
remain separate wellposedness requirements.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

namespace SourceBirkhoffMapComplexData

/-- The existing real Birkhoff map encodes exactly the new complex coordinates. -/
theorem encode_real_map (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (φ : realTypeSourceSubmodule p) :
    Birkhoff.encodeReal (sourceRealBirkhoffMap hp hp1 t φ) = sourceComplexBirkhoffMap hp hp1 t φ.val := by
  change Birkhoff.rectangularToComplex
    (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) (sourceRealBirkhoffMap hp hp1 t φ)) = _
  rw [D.real_map_complex_inclusion]
  rfl

/-- The complex-coordinate map retains injectivity of the actual real source map. -/
theorem complex_map_real_injective (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    Function.Injective (fun φ : realTypeSourceSubmodule p => sourceComplexBirkhoffMap hp hp1 t φ.val) := by
  intro φ ψ h
  apply D.proposition17_2
  apply Birkhoff.encodeReal_injective
  simpa only [D.encode_real_map] using h

end SourceBirkhoffMapComplexData
namespace SourceAbelianMomentAtlas

/-- Equation (4.15) using the actual global inverse on the real source space. -/
def renormalizedSourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) : realTypeSourceSubmodule p :=
  (D.realHomeomorph hp2).symm (Birkhoff.decodeReal (A.renormalizedPhaseTrajectory t φ τ))

/-- The lifted source has exactly the intended complex phase coordinates. -/
theorem complex_map_renormalizedSourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    sourceComplexBirkhoffMap hp hp1 t (A.renormalizedSourceFlow D hp2 φ τ).val =
      A.renormalizedPhaseTrajectory t φ τ := by
  rw [← D.encode_real_map]
  change Birkhoff.encodeReal ((D.realHomeomorph hp2)
    ((D.realHomeomorph hp2).symm (Birkhoff.decodeReal (A.renormalizedPhaseTrajectory t φ τ)))) = _
  rw [Homeomorph.apply_symm_apply]
  exact Birkhoff.encodeReal_decodeReal _ (A.renormalizedPhaseTrajectory_real D φ τ)

@[simp] theorem renormalizedSourceFlow_zero (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) : A.renormalizedSourceFlow D hp2 φ 0 = φ := by
  apply D.complex_map_real_injective
  dsimp only
  rw [A.complex_map_renormalizedSourceFlow D hp2, A.renormalizedPhaseTrajectory_zero]

/-- The lifted nonlinear flow preserves every original complex spectral action. -/
theorem renormalizedSourceFlow_action (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    sourceComplexAction hp hp1 n (A.renormalizedSourceFlow D hp2 φ τ).val =
      sourceComplexAction hp hp1 n φ.val := by
  rw [← D.complex_map_action _ (D.real_subset (A.renormalizedSourceFlow D hp2 φ τ).property) n,
    A.complex_map_renormalizedSourceFlow]
  exact A.renormalizedPhaseTrajectory_action D φ τ n

/-- Frequency invariance follows from preservation of the actual source actions. -/
theorem phaseFrequency_renormalizedSourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    A.phaseFrequency (A.renormalizedSourceFlow D hp2 φ τ) = A.phaseFrequency φ := by
  have hlevel : A.renormalizedSourceFlow D hp2 φ τ ∈ sourceRealActionLevelSet hp hp1 φ := by
    intro n
    have h := A.renormalizedSourceFlow_action D hp2 φ τ n
    rw [sourceComplexAction_eq_sourceRealAction hp hp1 n _ (A.renormalizedSourceFlow D hp2 φ τ).property,
      sourceComplexAction_eq_sourceRealAction hp hp1 n _ φ.property] at h
    exact congrArg Complex.re h
  funext n
  rw [phaseFrequency,phaseFrequency,A.renormalizedFrequency_real_eq_of_actions A hs hs φ
    (A.renormalizedSourceFlow D hp2 φ τ) hlevel n]

/-- The nonlinear source trajectories have the group law for all real times. -/
theorem renormalizedSourceFlow_add (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ σ : ℝ) :
    A.renormalizedSourceFlow D hp2 (A.renormalizedSourceFlow D hp2 φ σ) τ =
      A.renormalizedSourceFlow D hp2 φ (τ+σ) := by
  apply D.complex_map_real_injective
  dsimp only
  rw [A.complex_map_renormalizedSourceFlow D hp2, A.complex_map_renormalizedSourceFlow D hp2]
  simp only [renormalizedPhaseTrajectory, A.phaseFrequency_renormalizedSourceFlow hs D hp2,
    A.complex_map_renormalizedSourceFlow]
  exact Birkhoff.phaseFlow_add _ τ σ _

/-- Joint continuity in the original source norm, globally in time. -/
theorem continuous_renormalizedSourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2) :
    Continuous (fun x : ℝ × realTypeSourceSubmodule p => A.renormalizedSourceFlow D hp2 x.2 x.1) :=
  (D.realHomeomorph hp2).symm.continuous.comp
    (Birkhoff.decodeReal.continuous.comp (A.continuous_renormalizedPhaseTrajectory hs hP hrealP D))

/-- Every fixed time gives a homeomorphism whose inverse is the negative time map. -/
def renormalizedSourceHomeomorph (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2) (τ : ℝ) :
    realTypeSourceSubmodule p ≃ₜ realTypeSourceSubmodule p where
  toFun φ := A.renormalizedSourceFlow D hp2 φ τ
  invFun φ := A.renormalizedSourceFlow D hp2 φ (-τ)
  left_inv φ := by
    dsimp only
    rw [A.renormalizedSourceFlow_add hs.toSourcePsiIsolatingComplexExtension, neg_add_cancel,
    A.renormalizedSourceFlow_zero]
  right_inv φ := by
    dsimp only
    rw [A.renormalizedSourceFlow_add hs.toSourcePsiIsolatingComplexExtension, add_neg_cancel,
    A.renormalizedSourceFlow_zero]
  continuous_toFun := by
    simpa only [Function.comp_def] using!
      (A.continuous_renormalizedSourceFlow hs hP hrealP D hp2).comp
        (show Continuous (fun φ : realTypeSourceSubmodule p => (τ,φ)) from
          continuous_const.prodMk continuous_id)
  continuous_invFun := by
    simpa only [Function.comp_def] using!
      (A.continuous_renormalizedSourceFlow hs hP hrealP D hp2).comp
        (show Continuous (fun φ : realTypeSourceSubmodule p => (-τ,φ)) from
          continuous_const.prodMk continuous_id)

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
