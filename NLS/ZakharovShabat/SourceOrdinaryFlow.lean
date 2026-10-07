import NLS.ZakharovShabat.SourceOrdinaryPhaseTrajectory
import NLS.ZakharovShabat.SourceRenormalizedFlow
import NLS.Dynamics.RealComplexBirkhoffCoordinates
import NLS.ZakharovShabat.SourceBirkhoffGlobalInverse
import NLS.ZakharovShabat.SourceFrequencyActionInvariance

/-! # The ordinary NLS source flow for 1 < p ≤ 2

The actual Birkhoff inverse lifts the mass-corrected phase trajectories.
Every original action and the physical mass are conserved. The full
nonlinear flow is a continuous group with negative time as inverse.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

namespace SourceAbelianMomentAtlas

/-- Equation (4.16) using the actual global inverse on the real source space. -/
def ordinarySourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) : realTypeSourceSubmodule p :=
  (D.realHomeomorph hp2).symm (Birkhoff.decodeReal (A.ordinaryPhaseTrajectory t hp2 φ τ))

/-- The lifted source has exactly the intended complex phase coordinates. -/
theorem complex_map_ordinarySourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    sourceComplexBirkhoffMap hp hp1 t (A.ordinarySourceFlow D hp2 φ τ).val =
      A.ordinaryPhaseTrajectory t hp2 φ τ := by
  rw [← D.encode_real_map]
  change Birkhoff.encodeReal ((D.realHomeomorph hp2)
    ((D.realHomeomorph hp2).symm (Birkhoff.decodeReal (A.ordinaryPhaseTrajectory t hp2 φ τ)))) = _
  rw [Homeomorph.apply_symm_apply]
  exact Birkhoff.encodeReal_decodeReal _ (A.ordinaryPhaseTrajectory_real D hp2 φ τ)

@[simp] theorem ordinarySourceFlow_zero (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) : A.ordinarySourceFlow D hp2 φ 0 = φ := by
  apply D.complex_map_real_injective
  dsimp only
  rw [A.complex_map_ordinarySourceFlow D hp2, A.ordinaryPhaseTrajectory_zero]

/-- The lifted nonlinear flow preserves every original complex spectral action. -/
theorem ordinarySourceFlow_action (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    sourceComplexAction hp hp1 n (A.ordinarySourceFlow D hp2 φ τ).val =
      sourceComplexAction hp hp1 n φ.val := by
  rw [← D.complex_map_action _ (D.real_subset (A.ordinarySourceFlow D hp2 φ τ).property) n,
    A.complex_map_ordinarySourceFlow]
  exact A.ordinaryPhaseTrajectory_action D hp2 φ τ n

/-- The ordinary flow conserves the physical mass as well as every action. -/
theorem ordinarySourceFlow_mass (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    sourceOrdinaryMass hp2 (A.ordinarySourceFlow D hp2 φ τ) = sourceOrdinaryMass hp2 φ :=
  sourceOrdinaryMass_eq_of_actions hp hp1 hp2 _ φ (A.ordinarySourceFlow_action D hp2 φ τ)

/-- Frequency invariance follows from preservation of the actual source actions. -/
theorem ordinaryPhaseFrequency_ordinarySourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    A.ordinaryPhaseFrequency hp2 (A.ordinarySourceFlow D hp2 φ τ) = A.ordinaryPhaseFrequency hp2 φ := by
  have hlevel : A.ordinarySourceFlow D hp2 φ τ ∈ sourceRealActionLevelSet hp hp1 φ := by
    intro n
    have h := A.ordinarySourceFlow_action D hp2 φ τ n
    rw [sourceComplexAction_eq_sourceRealAction hp hp1 n _ (A.ordinarySourceFlow D hp2 φ τ).property,
      sourceComplexAction_eq_sourceRealAction hp hp1 n _ φ.property] at h
    exact congrArg Complex.re h
  funext n
  rw [ordinaryPhaseFrequency,ordinaryPhaseFrequency,A.renormalizedFrequency_real_eq_of_actions A hs hs φ
    (A.ordinarySourceFlow D hp2 φ τ) hlevel n,
    sourceOrdinaryMass_eq_of_actions hp hp1 hp2 _ φ (A.ordinarySourceFlow_action D hp2 φ τ)]

/-- The nonlinear source trajectories have the group law for all real times. -/
theorem ordinarySourceFlow_add (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ σ : ℝ) :
    A.ordinarySourceFlow D hp2 (A.ordinarySourceFlow D hp2 φ σ) τ =
      A.ordinarySourceFlow D hp2 φ (τ+σ) := by
  apply D.complex_map_real_injective
  dsimp only
  rw [A.complex_map_ordinarySourceFlow D hp2, A.complex_map_ordinarySourceFlow D hp2]
  simp only [ordinaryPhaseTrajectory, A.ordinaryPhaseFrequency_ordinarySourceFlow hs D hp2,
    A.complex_map_ordinarySourceFlow]
  exact Birkhoff.phaseFlow_add _ τ σ _

/-- Joint continuity in the original source norm, globally in time. -/
theorem continuous_ordinarySourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2) :
    Continuous (fun x : ℝ × realTypeSourceSubmodule p => A.ordinarySourceFlow D hp2 x.2 x.1) :=
  (D.realHomeomorph hp2).symm.continuous.comp
    (Birkhoff.decodeReal.continuous.comp (A.continuous_ordinaryPhaseTrajectory hs hP hrealP D hp2))

/-- Every fixed time gives a homeomorphism whose inverse is the negative time map. -/
def ordinarySourceHomeomorph (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hrealP : realTypeSourceLocus p ⊆ P)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2) (τ : ℝ) :
    realTypeSourceSubmodule p ≃ₜ realTypeSourceSubmodule p where
  toFun φ := A.ordinarySourceFlow D hp2 φ τ
  invFun φ := A.ordinarySourceFlow D hp2 φ (-τ)
  left_inv φ := by
    dsimp only
    rw [A.ordinarySourceFlow_add hs.toSourcePsiIsolatingComplexExtension, neg_add_cancel,
    A.ordinarySourceFlow_zero]
  right_inv φ := by
    dsimp only
    rw [A.ordinarySourceFlow_add hs.toSourcePsiIsolatingComplexExtension, add_neg_cancel,
    A.ordinarySourceFlow_zero]
  continuous_toFun := by
    simpa only [Function.comp_def] using!
      (A.continuous_ordinarySourceFlow hs hP hrealP D hp2).comp
        (show Continuous (fun φ : realTypeSourceSubmodule p => (τ,φ)) from
          continuous_const.prodMk continuous_id)
  continuous_invFun := by
    simpa only [Function.comp_def] using!
      (A.continuous_ordinarySourceFlow hs hP hrealP D hp2).comp
        (show Continuous (fun φ : realTypeSourceSubmodule p => (-τ,φ)) from
          continuous_const.prodMk continuous_id)

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
