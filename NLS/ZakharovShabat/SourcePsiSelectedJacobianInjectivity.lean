import NLS.ZakharovShabat.SourcePsiSelectedKernelGapZeroSequence
import NLS.ZakharovShabat.SourcePsiInterpolationQuotientExterior

/-!
# Injectivity of the selected psi root Jacobian

At real source data, a real kernel direction has a zero of its entire
variation in every retained periodic gap. The simple gap product and
interpolation uniqueness force that direction to vanish. Splitting a
complex kernel direction into real and imaginary parts then proves
injectivity of the bounded complex Jacobian.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The gap-zero interpolation proof kills each real selected-Jacobian
kernel direction under one common isolating-disc geometry. -/
theorem sourcePsiSelectedRootJacobian_realKernel_eq_zero_of_gapGeometry
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (hrootloc : ∀ j : ℤ,
      displacedRoots (a : Coeff p) j ∈
        sourceIsolatingDisc hp hp1 φ N ε j)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (hcenter : ∀ m : ℤ, ∃ x : ℝ, c m = (x:ℂ))
    (hR : ∀ m : ℤ, 0 < R m)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m))
    (hfilled : ∀ m : ℤ, closedBall (c m) (R m) ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdom : ∀ m : ℤ,
      closedBall (c m) (R m) ⊆
        sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : ∀ m : ℤ,
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (v : DeletedCoeff p n)
    (hvreal : ∀ j : ℤ, ((v : Coeff p) j).im = 0)
    (hvkernel : sourcePsiSelectedRootJacobian hp hp1 n c R a ψ v = 0) :
    v = 0 := by
  obtain ⟨ρ,_,_,hρ⟩ :=
    exists_sourcePsiSelectedJacobian_realKernel_gapZero_sequence
      hp hp1 n c R U hUopen hcoord hdiff a ψ hpair hψ hroots
        hcenter hR hseg hdom hcircle v hvreal hvkernel
  have hsegIso : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ N ε m := by
    intro m z hz
    exact hfilled m (ball_subset_closedBall (hseg m hz))
  have hsep : Function.Injective (displacedRoots (a : Coeff p)) :=
    displacedRoots_injective_of_isolatingDiscs
      hp hp1 φ N ε (a : Coeff p) hrootloc hdisjoint
  have hvzero : (v : Coeff p) = 0 := by
    apply sourcePsiCandidate_deleted_direction_zero_of_gapZeros
      hp hp1 φ ψ N ε n (a : Coeff p) (v : Coeff p)
        hsep v.property hsegIso (hrootloc n) hdisjoint
    intro m hmn
    exact ⟨ρ m,(hρ m hmn).1,(hρ m hmn).2⟩
  exact Subtype.ext hvzero

/-- Real and imaginary kernel directions both vanish, so the bounded
selected psi root Jacobian has trivial kernel. -/
theorem sourcePsiSelectedRootJacobian_kernel_eq_zero_of_gapGeometry
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (hrealSeq : ∀ t ∈ U,
      IsRealType (CoeffPair.toMax p t.2) →
      (∀ j : ℤ, (displacedRoots (t.1 : Coeff p) j).im = 0) →
        ∀ m : ℤ,
          ((sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 :
            Coeff p) m).im = 0)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (hrootloc : ∀ j : ℤ,
      displacedRoots (a : Coeff p) j ∈
        sourceIsolatingDisc hp hp1 φ N ε j)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (hcenter : ∀ m : ℤ, ∃ x : ℝ, c m = (x:ℂ))
    (hR : ∀ m : ℤ, 0 < R m)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m))
    (hfilled : ∀ m : ℤ, closedBall (c m) (R m) ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdom : ∀ m : ℤ,
      closedBall (c m) (R m) ⊆
        sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : ∀ m : ℤ,
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (v : DeletedCoeff p n)
    (hvkernel : sourcePsiSelectedRootJacobian hp hp1 n c R a ψ v = 0) :
    v = 0 := by
  obtain ⟨hre,him⟩ := sourcePsiSelectedRootJacobian_kernel_realImag
    hp hp1 n c R U hUopen hdiff hrealSeq a ψ hpair hψ hroots v hvkernel
  have hrzero := sourcePsiSelectedRootJacobian_realKernel_eq_zero_of_gapGeometry
    hp hp1 φ N ε n c R U hUopen hcoord hdiff a ψ hpair hψ hroots
      hrootloc hdisjoint hcenter hR hseg hfilled hdom hcircle
      (DeletedCoeff.realPart v) (DeletedCoeff.realPart_im_eq_zero v) hre
  have hizero := sourcePsiSelectedRootJacobian_realKernel_eq_zero_of_gapGeometry
    hp hp1 φ N ε n c R U hUopen hcoord hdiff a ψ hpair hψ hroots
      hrootloc hdisjoint hcenter hR hseg hfilled hdom hcircle
      (DeletedCoeff.imagPart v) (DeletedCoeff.imagPart_im_eq_zero v) him
  calc
    v = DeletedCoeff.realPart v + I • DeletedCoeff.imagPart v :=
      (DeletedCoeff.realPart_add_I_imagPart v).symm
    _ = 0 := by rw [hrzero,hizero]; simp

/-- The selected psi root Jacobian is injective wherever the common
contour family and isolating-disc conditions hold. -/
theorem sourcePsiSelectedRootJacobian_injective_of_gapGeometry
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (hrealSeq : ∀ t ∈ U,
      IsRealType (CoeffPair.toMax p t.2) →
      (∀ j : ℤ, (displacedRoots (t.1 : Coeff p) j).im = 0) →
        ∀ m : ℤ,
          ((sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 :
            Coeff p) m).im = 0)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (hrootloc : ∀ j : ℤ,
      displacedRoots (a : Coeff p) j ∈
        sourceIsolatingDisc hp hp1 φ N ε j)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (hcenter : ∀ m : ℤ, ∃ x : ℝ, c m = (x:ℂ))
    (hR : ∀ m : ℤ, 0 < R m)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m))
    (hfilled : ∀ m : ℤ, closedBall (c m) (R m) ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdom : ∀ m : ℤ,
      closedBall (c m) (R m) ⊆
        sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : ∀ m : ℤ,
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    Function.Injective (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) := by
  intro x y hxy
  have hker : sourcePsiSelectedRootJacobian hp hp1 n c R a ψ (x-y) = 0 := by
    rw [map_sub,hxy,sub_self]
  exact sub_eq_zero.mp
    (sourcePsiSelectedRootJacobian_kernel_eq_zero_of_gapGeometry
      hp hp1 φ N ε n c R U hUopen hcoord hdiff hrealSeq a ψ hpair hψ
        hroots hrootloc hdisjoint hcenter hR hseg hfilled hdom hcircle
        (x-y) hker)

end NLS.ZakharovShabat
