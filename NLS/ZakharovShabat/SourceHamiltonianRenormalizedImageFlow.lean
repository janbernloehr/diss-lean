import NLS.ZakharovShabat.SourceRenormalizedLocalExistence
import NLS.ZakharovShabat.SourceHamiltonianRenormalizedTrajectories

/-! # Physical time orientation on the actual renormalized image domain

Time reflection gives local source dynamics with the Hamiltonian signs.
Regularity and path evaluation retain their explicit admissibility guard;
no conclusion uses the total inverse outside its actual Birkhoff image.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P V B X : Set (CoeffPair p)}
variable {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual image flow with the physical Hamiltonian time orientation. -/
def hamiltonianRenormalizedImageFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (φ : realTypeSourceSubmodule p) (time : ℝ) : realTypeSourceSubmodule p :=
  A.renormalizedImageFlow D φ (-time)

@[simp] theorem hamiltonianRenormalizedImageFlow_zero (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (φ : realTypeSourceSubmodule p) :
    A.hamiltonianRenormalizedImageFlow D φ 0 = φ := by simp [hamiltonianRenormalizedImageFlow]

/-- The physical group law wherever the initial flow step is admissible. -/
theorem hamiltonianRenormalizedImageFlow_add (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (φ : realTypeSourceSubmodule p) (time r : ℝ)
    (hr : (-r,φ) ∈ A.renormalizedImageDomain t) :
    A.hamiltonianRenormalizedImageFlow D (A.hamiltonianRenormalizedImageFlow D φ r) time =
      A.hamiltonianRenormalizedImageFlow D φ (time+r) := by
  simp only [hamiltonianRenormalizedImageFlow,A.renormalizedImageFlow_add hs D φ (-time) (-r) hr,neg_add]

/-- The physical source path on a symmetric compact interval. -/
def hamiltonianRenormalizedImageTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (T : ℝ)
    (φ : realTypeSourceSubmodule p) : C(Icc (-T) T,realTypeSourceSubmodule p) :=
  (A.renormalizedImageTrajectoryOn D T φ).comp (hamiltonianTimeReflection T)

/-- Path evaluation is the actual source flow on the asserted domain. -/
theorem hamiltonianRenormalizedImageTrajectoryOn_apply (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (T : ℝ) (φ : realTypeSourceSubmodule p) (hφ : φ ∈ A.renormalizedTrajectoryDomain t T)
    (time : Icc (-T) T) :
    A.hamiltonianRenormalizedImageTrajectoryOn D T φ time =
      A.hamiltonianRenormalizedImageFlow D φ time.val :=
  A.renormalizedImageTrajectoryOn_apply hs hP hr D T φ hφ (hamiltonianTimeReflection T time)

/-- Analyticity in the complete compact-time source norm survives time reflection. -/
theorem analytic_hamiltonianRenormalizedImageTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (T : ℝ) :
    AnalyticOnNhd ℝ (A.hamiltonianRenormalizedImageTrajectoryOn D T)
      (A.renormalizedTrajectoryDomain t T) := by
  intro φ hφ
  exact ((ContinuousMap.compCLM ℝ (realTypeSourceSubmodule p) (hamiltonianTimeReflection T)).analyticAt _).comp
    (A.analytic_renormalizedImageTrajectoryOn hs hP hr D T φ hφ)

/-- Joint continuity on any source neighborhood whose trajectories stay admissible. -/
theorem continuousOn_hamiltonianRenormalizedImageFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (U : Set (realTypeSourceSubmodule p))
    (hU : ∀ φ ∈ U, ∀ time : ℝ, (time,φ) ∈ A.renormalizedImageDomain t) :
    ContinuousOn (fun x : ℝ × realTypeSourceSubmodule p => A.hamiltonianRenormalizedImageFlow D x.2 x.1)
      (univ ×ˢ U) := by
  have hg : Continuous (fun x : ℝ × realTypeSourceSubmodule p => (-x.1,x.2)) :=
    continuous_fst.neg.prodMk continuous_snd
  have hmap : MapsTo (fun x : ℝ × realTypeSourceSubmodule p => (-x.1,x.2))
      (univ ×ˢ U) (A.renormalizedImageDomain t) := fun x hx => hU x.2 hx.2 (-x.1)
  have hc := (A.continuousOn_renormalizedImageFlow hs hP hr D).comp hg.continuousOn hmap
  change ContinuousOn (fun x : ℝ × realTypeSourceSubmodule p => A.renormalizedImageFlow D x.2 (-x.1))
    (univ ×ˢ U) at hc
  exact hc

/-- In the surjective exponent range, the image and global physical flows coincide. -/
theorem hamiltonianRenormalizedImageFlow_eq_global (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (time : ℝ) :
    A.hamiltonianRenormalizedImageFlow D φ time = A.hamiltonianRenormalizedSourceFlow D hp2 φ time :=
  A.renormalizedImageFlow_eq_global D hp2 φ (-time)

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
