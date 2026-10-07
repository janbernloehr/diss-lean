import NLS.Dynamics.UnboundedPhaseObstruction
import NLS.ZakharovShabat.SourceFiniteGapOrdinaryTrajectory
import NLS.ZakharovShabat.SourceBirkhoffImageInverse
import Mathlib.Topology.ContinuousMap.Star

/-! # No continuous extension of ordinary NLS coordinates outside the Hilbert locus

Even agreement on actual finite-gap sources prevents continuity of an
ordinary coordinate trajectory at a non-Hilbert source with nonzero
initial amplitude. The result is transferred to the actual Birkhoff
image using its proved homeomorphism with the source space.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The finite-gap second coordinate is the conjugate of the first along the real flow. -/
theorem finiteGapOrdinaryCoordinateSnd_eq_star (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (T : ℝ)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    A.finiteGapOrdinaryCoordinateSnd t T φ hf n = star (A.finiteGapOrdinaryCoordinate t T φ hf n) := by
  apply ContinuousMap.ext
  intro τ
  change Complex.exp _ * _ = conj (Complex.exp _ * _)
  rw [map_mul,← Complex.exp_conj,D.complex_map_real φ n]
  congr 2
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

/-- No scalar trajectory extension can be continuous at a non-Hilbert source with nonzero first amplitude. -/
theorem not_continuousAt_ordinaryCoordinate_extension (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (h2p : 2 ≤ p) (T : ℝ) (hT : 0 < T) (φ : realTypeSourceSubmodule p)
    (hφ : φ ∉ sourceHilbertLocus h2p) (n : ℤ) (hn : (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n ≠ 0)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,ℂ))
    (he : ∀ ψ : realTypeSourceSubmodule p, ∀ hf : ψ ∈ sourceFiniteGapLocus hp hp1, F ψ = A.finiteGapOrdinaryCoordinate t T ψ hf n) :
    ¬ ContinuousAt F φ := by
  intro hF
  obtain ⟨ψ,hf,hψ⟩ := exists_sourceFiniteGap_sequence hp hp1 φ
  have hamp : Tendsto (fun j => (sourceComplexBirkhoffMap hp hp1 t (ψ j).val).1 n) atTop
      (𝓝 ((sourceComplexBirkhoffMap hp hp1 t φ.val).1 n)) :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp D.continuous_complex_map_real.fst).continuousAt.tendsto.comp hψ
  apply NLS.Dynamics.not_tendsto_phase_trajectories T hT
    (fun j => A.finiteGapOrdinaryFrequency (ψ j) (hf j) n)
    (fun j => (sourceComplexBirkhoffMap hp hp1 t (ψ j).val).1 n) _ hn
    (A.tendsto_finiteGapOrdinaryFrequency_atTop hs hP hr h2p φ hφ ψ hf hψ n) hamp
    (fun j => F (ψ j)) (fun j τ => ?_) (F φ) (hF.tendsto.comp hψ)
  rw [he (ψ j) (hf j)]
  rfl

/-- The same nonextension result holds for the opposite-sign second coordinate. -/
theorem not_continuousAt_ordinaryCoordinateSnd_extension (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (h2p : 2 ≤ p) (T : ℝ) (hT : 0 < T) (φ : realTypeSourceSubmodule p)
    (hφ : φ ∉ sourceHilbertLocus h2p) (n : ℤ) (hn : (sourceComplexBirkhoffMap hp hp1 t φ.val).2 n ≠ 0)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,ℂ))
    (he : ∀ ψ : realTypeSourceSubmodule p, ∀ hf : ψ ∈ sourceFiniteGapLocus hp hp1, F ψ = A.finiteGapOrdinaryCoordinateSnd t T ψ hf n) :
    ¬ ContinuousAt F φ := by
  intro hF
  have hn1 : (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n ≠ 0 := by
    intro h
    apply hn
    rw [D.complex_map_real φ n,h,map_zero]
  apply A.not_continuousAt_ordinaryCoordinate_extension hs hP hr D h2p T hT φ hφ n hn1
    (fun ψ => star (F ψ)) (fun ψ hf => ?_) hF.star
  rw [he ψ hf,A.finiteGapOrdinaryCoordinateSnd_eq_star D,star_star]

/-- The first-coordinate obstruction also holds with initial data in the actual open Birkhoff image. -/
theorem not_continuousAt_ordinaryCoordinate_image_extension (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (h2p : 2 ≤ p) (T : ℝ) (hT : 0 < T) (φ : realTypeSourceSubmodule p)
    (hφ : φ ∉ sourceHilbertLocus h2p) (n : ℤ) (hn : (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n ≠ 0)
    (F : range (sourceRealBirkhoffMap hp hp1 t) → C(Icc (0 : ℝ) T,ℂ))
    (he : ∀ ψ : realTypeSourceSubmodule p, ∀ hf : ψ ∈ sourceFiniteGapLocus hp hp1,
      F (D.realImageHomeomorph ψ) = A.finiteGapOrdinaryCoordinate t T ψ hf n) :
    ¬ ContinuousAt F (D.realImageHomeomorph φ) := by
  intro hF
  exact A.not_continuousAt_ordinaryCoordinate_extension hs hP hr D h2p T hT φ hφ n hn
    (fun ψ => F (D.realImageHomeomorph ψ)) he
    (hF.comp D.realImageHomeomorph.continuous.continuousAt)

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
