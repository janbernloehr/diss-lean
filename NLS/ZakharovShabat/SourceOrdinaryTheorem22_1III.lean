import NLS.ZakharovShabat.SourceOrdinaryCoordinateObstruction
import NLS.ZakharovShabat.SourceComplexBirkhoffExponent

/-! # Theorem 22.1(iii): ordinary coordinate nonextension on the Birkhoff image

At a coordinate point outside ell², neither nonzero complex component
admits a continuous compact-time trajectory extension agreeing with the
actual ordinary finite-gap dynamics. The initial-data domain is the actual
Birkhoff image, parameterized by the real rectangular coordinates; the
trajectory values are Section 22's complex coordinates.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

private def positiveTimeInclusion (T : ℝ) (hT : 0 < T) : C(Icc (0 : ℝ) T,Icc (-T) T) where
  toFun τ := ⟨τ.val,by constructor; linarith [τ.property.1]; exact τ.property.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The first complex coordinate cannot extend continuously on any [-T,T] at a non-ell² image point. -/
theorem theorem22_1_iii_fst (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (h2p : 2 ≤ p) (T : ℝ) (hT : 0 < T) (φ : realTypeSourceSubmodule p)
    (hφ : ¬ Summable (fun k : ℤ => ‖(sourceComplexBirkhoffMap hp hp1 t φ.val).1 k‖^2))
    (n : ℤ) (hn : (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n ≠ 0)
    (F : range (sourceRealBirkhoffMap hp hp1 t) → C(Icc (-T) T,ℂ))
    (he : ∀ ψ : realTypeSourceSubmodule p, ∀ hf : ψ ∈ sourceFiniteGapLocus hp hp1,
      ∀ τ : Icc (-T) T, F (D.realImageHomeomorph ψ) τ =
        Complex.exp (((τ.val*A.finiteGapOrdinaryFrequency ψ hf n : ℝ) : ℂ)*Complex.I)*
          (sourceComplexBirkhoffMap hp hp1 t ψ.val).1 n) :
    ¬ ContinuousAt F (D.realImageHomeomorph φ) := by
  intro hF
  have hnon : φ ∉ sourceHilbertLocus h2p :=
    fun h => hφ (D.summable_complex_map_fst_of_mem_hilbert h2p φ h)
  let r := positiveTimeInclusion T hT
  apply A.not_continuousAt_ordinaryCoordinate_image_extension hs hP hr D h2p T hT φ hnon n hn
    (fun z => (F z).comp r) (fun ψ hf => ?_)
    ((ContinuousMap.continuous_precomp r).continuousAt.comp hF)
  apply ContinuousMap.ext
  intro τ
  exact he ψ hf (r τ)

/-- The opposite-sign second complex coordinate has the same nonextension obstruction. -/
theorem theorem22_1_iii_snd (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (h2p : 2 ≤ p) (T : ℝ) (hT : 0 < T) (φ : realTypeSourceSubmodule p)
    (hφ : ¬ Summable (fun k : ℤ => ‖(sourceComplexBirkhoffMap hp hp1 t φ.val).1 k‖^2))
    (n : ℤ) (hn : (sourceComplexBirkhoffMap hp hp1 t φ.val).2 n ≠ 0)
    (F : range (sourceRealBirkhoffMap hp hp1 t) → C(Icc (-T) T,ℂ))
    (he : ∀ ψ : realTypeSourceSubmodule p, ∀ hf : ψ ∈ sourceFiniteGapLocus hp hp1,
      ∀ τ : Icc (-T) T, F (D.realImageHomeomorph ψ) τ =
        Complex.exp (((-τ.val*A.finiteGapOrdinaryFrequency ψ hf n : ℝ) : ℂ)*Complex.I)*
          (sourceComplexBirkhoffMap hp hp1 t ψ.val).2 n) :
    ¬ ContinuousAt F (D.realImageHomeomorph φ) := by
  intro hF
  have hnon : φ ∉ sourceHilbertLocus h2p :=
    fun h => hφ (D.summable_complex_map_fst_of_mem_hilbert h2p φ h)
  let r := positiveTimeInclusion T hT
  apply A.not_continuousAt_ordinaryCoordinateSnd_extension hs hP hr D h2p T hT φ hnon n hn
    (fun ψ => (F (D.realImageHomeomorph ψ)).comp r) (fun ψ hf => ?_)
    ((ContinuousMap.continuous_precomp r).continuousAt.comp
      (hF.comp D.realImageHomeomorph.continuous.continuousAt))
  apply ContinuousMap.ext
  intro τ
  exact he ψ hf (r τ)

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
