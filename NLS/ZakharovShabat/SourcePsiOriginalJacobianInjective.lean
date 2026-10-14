import NLS.ZakharovShabat.SourcePsiOriginalKernelContour
import NLS.ZakharovShabat.SourcePsiOriginalGapInterpolation
import NLS.ZakharovShabat.SourcePsiOriginalOuterCircles

/-!
# Injectivity of the original psi root Jacobian

Real kernel vectors give gap zeros of their entire variation. The
interpolation argument on the original disk family kills the variation
and then the direction. Real matrix entries reduce every complex
kernel vector to two real kernel vectors. All root inputs, contours,
and source points belong to the original domain.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real kernel direction has identically zero entire variation. -/
theorem SourceLemma12_4Data.originalRealKernel_variation_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_4Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (a : Coeff p)
    (ha : a ∈ sourcePsiOriginalRootPlacement D) (haReal : ∀ k : ℤ, (a k).im = 0)
    (h : DeletedCoeff p n) (hr : ∀ k : ℤ, ((h:Coeff p) k).im = 0)
    (hker : sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ h = 0) :
    sourcePsiCandidateVariation n a (h:Coeff p) = 0 :=
  hD.originalVariation_zero_of_gapZeros ψ hψV n a (h:Coeff p) ha h.property
    (H.originalRealKernel_gapZero hD ψ hψW hψV hreal n a haReal h hr hker)

/-- The original simple roots recover every coefficient of a real kernel direction. -/
theorem SourceLemma12_4Data.originalRealKernel_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_4Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (a : Coeff p)
    (ha : a ∈ sourcePsiOriginalRootPlacement D) (haReal : ∀ k : ℤ, (a k).im = 0)
    (h : DeletedCoeff p n) (hr : ∀ k : ℤ, ((h:Coeff p) k).im = 0)
    (hker : sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ h = 0) : h = 0 := by
  apply Subtype.ext
  apply sourcePsiCandidateVariation_zero_imp_deleted_direction_zero hp hp1 n a (h:Coeff p)
    (hD.originalRootPlacement_injective a ha) h.property
  intro z
  exact congrFun (H.originalRealKernel_variation_eq_zero hD ψ hψW hψV hreal n a ha haReal h hr hker) z

/-- The full complex kernel of the original bounded Jacobian is trivial. -/
theorem SourceLemma12_4Data.originalKernel_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_4Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (a : Coeff p)
    (ha : a ∈ sourcePsiOriginalRootPlacement D) (haReal : ∀ k : ℤ, (a k).im = 0)
    (h : DeletedCoeff p n)
    (hker : sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ h = 0) : h = 0 := by
  obtain ⟨hre,him⟩ := H.originalKernel_realImag ψ hψW hreal n a haReal h hker
  have hrzero := H.originalRealKernel_eq_zero hD ψ hψW hψV hreal n a ha haReal
    (DeletedCoeff.realPart h) (DeletedCoeff.realPart_im_eq_zero h) hre
  have hizero := H.originalRealKernel_eq_zero hD ψ hψW hψV hreal n a ha haReal
    (DeletedCoeff.imagPart h) (DeletedCoeff.imagPart_im_eq_zero h) him
  calc
    h = DeletedCoeff.realPart h+Complex.I • DeletedCoeff.imagPart h :=
      (DeletedCoeff.realPart_add_I_imagPart h).symm
    _ = 0 := by rw [hrzero,hizero]; simp

/-- Lemma 12.7's injectivity for the actual original-domain Jacobian. -/
theorem SourceLemma12_4Data.originalRootJacobian_injective
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_4Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (a : Coeff p)
    (ha : a ∈ sourcePsiOriginalRootPlacement D) (haReal : ∀ k : ℤ, (a k).im = 0) :
    Function.Injective (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply H.originalKernel_eq_zero hD ψ hψW hψV hreal n a ha haReal (x-y)
  rw [map_sub,hxy,sub_self]

end NLS.ZakharovShabat
