import NLS.ZakharovShabat.SourceGapSymmetries
import NLS.ZakharovShabat.SourceInvariantNeighborhood
import NLS.ZakharovShabat.SourcePrimitiveGradientSymmetries
import NLS.Articles.MKdVNLSHierarchies.PointwiseSpectralSymmetries

/-! # The invariant neighborhood and literal gap interfaces in Theorem 6

The neighborhood may be chosen inside any supplied open almost-real domain,
so all existing spectral setup properties survive the shrinking. A common
invariant neighborhood also carries the actual root and primitive differential.
The pointwise primitive-gradient symmetries are valid on its cut complement;
no assertion of the still-separate Corollary8 primitive-value identities is made.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.MKdVNLSHierarchies
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem theorem6_invariant_neighborhood_inside (X : Set (CoeffPair p))
    (hX : IsOpen X) (hreal : realTypeSourceLocus p ⊆ X) :
    ∃ V : Set (CoeffPair p), V ⊆ X ∧ IsOpen V ∧ IsConnected V ∧ realTypeSourceLocus p ⊆ V ∧
      MapsTo sourceComponentSwap V V ∧ MapsTo sourceMidpointReflection V V ∧
      ∀ α : ℝ, MapsTo (sourcePhaseRotation α) V V := by
  refine ⟨sourceConnectedSymmetryCore X,sourceConnectedSymmetryCore_subset X,
    isOpen_sourceConnectedSymmetryCore X hX,isConnected_sourceConnectedSymmetryCore X hreal,
    realTypeSourceLocus_subset_sourceConnectedSymmetryCore X hreal,
    sourceConnectedSymmetryCore_componentSwap X hreal,
    sourceConnectedSymmetryCore_midpointReflection X hreal,?_⟩
  intro α
  exact sourceConnectedSymmetryCore_circleRotation X hreal (Circle.exp α)

theorem theorem6_i_gap_segments (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (α : ℝ) (n : ℤ) (z : ℂ) :
    (-z ∈ sourcePeriodicSegment hp hp1 (sourceComponentSwap φ) (-n) ↔
      z ∈ sourcePeriodicSegment hp hp1 φ n) ∧
    (-z ∈ sourcePeriodicSegment hp hp1 (sourceMidpointReflection φ) (-n) ↔
      z ∈ sourcePeriodicSegment hp hp1 φ n) ∧
    sourcePeriodicSegment hp hp1 (sourcePhaseRotation α φ) n = sourcePeriodicSegment hp hp1 φ n :=
  ⟨sourcePeriodicSegment_componentSwap hp hp1 φ n z,
   sourcePeriodicSegment_midpointReflection hp hp1 φ n z,
   sourcePeriodicSegment_reciprocalScaling hp hp1 _ (exp_ne_zero _) φ n⟩

theorem theorem6_invariant_root_primitive_neighborhood :
    ∃ A V : Set (CoeffPair 2),
      IsOpen V ∧ IsConnected V ∧ realTypeSourceLocus 2 ⊆ V ∧
      MapsTo sourceComponentSwap V V ∧ MapsTo sourceMidpointReflection V V ∧
      (∀ α : ℝ, MapsTo (sourcePhaseRotation α) V V) ∧
      IsOpen (sourceCanonicalRootJointDomain (by simp) (by norm_num) V) ∧
      AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct (by simp) (by norm_num))
        (sourceCanonicalRootJointDomain (by simp) (by norm_num) V) ∧
      SourceFullAbelianDifferentialData (by simp) (by norm_num) A V := by
  obtain ⟨A,V,hV,hconn,hreal,hP,hT,hR,hDom,hroot,D⟩ :=
    exists_sourceInvariantPrimitiveNeighborhood (p := 2) (by simp) (by norm_num)
  exact ⟨A,V,hV,hconn,hreal,hP,hT,fun α => hR (Circle.exp α),hDom,hroot,D⟩

/-- Corollary8's pointwise gradient clause, in forward covariance form.
On the invariant neighborhood's full cut complement these are the unique
continuous periodic representatives of the actual full primitive derivatives. -/
theorem corollary8_physical_gradient_symmetries (φ : CoeffPair 2) (α : ℝ) (z : ℂ) (x : ℝ) :
    sourceFullAbelianPhysicalGradient (sourceComponentSwap φ) (-z) x =
        (-(sourceFullAbelianPhysicalGradient φ z x).2,-(sourceFullAbelianPhysicalGradient φ z x).1) ∧
    sourceFullAbelianPhysicalGradient (sourceMidpointReflection φ) (-z) x =
        -sourceFullAbelianPhysicalGradient φ z (1-x) ∧
    sourceFullAbelianPhysicalGradient (sourcePhaseRotation α φ) z x =
        ((exp ((α:ℂ)*I))⁻¹*(sourceFullAbelianPhysicalGradient φ z x).1,
         exp ((α:ℂ)*I)*(sourceFullAbelianPhysicalGradient φ z x).2) :=
  ⟨sourceFullAbelianPhysicalGradient_componentSwap φ z x,
   sourceFullAbelianPhysicalGradient_midpointReflection φ z x,
   sourceFullAbelianPhysicalGradient_reciprocalScaling _ (exp_ne_zero _) φ z x⟩

end NLS.Articles.MKdVNLSHierarchies
