import NLS.ZakharovShabat.SourcePsiFullProductInterpolation
import NLS.ZakharovShabat.SourcePsiLimitKernelGapZeros

/-!
# Vanishing of real directions in the limit operator's kernel

The actual limit operator supplies one full gap-zero sequence for a
real kernel direction. Full-product interpolation forces its entire
variation to vanish, and the simple original roots recover the zero
direction. Norm convergence and compactness remain on that same
operator and real-centered contour family.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every real direction in the bounded contour-limit operator's
kernel vanishes, by full gap-zero interpolation. -/
theorem sourcePsiLimitMatrixOperator_realKernel_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (c : ℤ → ℂ) (R : ℤ → ℝ) (hcenter : ∀ m : ℤ, (c m).im = 0)
    (hgeom : ∀ m : ℤ,
      0 < R m ∧ sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
      closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m ∧
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (Qstar : Coeff p →L[ℂ] Coeff p)
    (hentry : ∀ m k : ℤ, (Qstar (lp.single p k 1)) m =
      sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m))
    (h : Coeff p) (hreal : ∀ k : ℤ, (h k).im = 0) (hkernel : Qstar h = 0) : h = 0 := by
  obtain ⟨ρ,hρlp,hρ⟩ := exists_sourcePsiLimitMatrixOperator_realKernel_gapZero_sequence
    hp hp1 a φ hφ ha c R hcenter hgeom Qstar hentry h hreal hkernel
  exact sourcePsiFullProductVariation_direction_zero_of_gapZero_sequence
    hp hp1 φ hφ ρ hρlp (fun m => (hρ m).1) a h ha (fun m => (hρ m).2)

/-- The actual fixed-root norm-limit operator is a compact
perturbation of `2I` and has no nonzero real kernel directions. -/
theorem exists_sourcePsiLimitMatrixOperator_normLimit_realKernelZero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ, (c m).im = 0) ∧
      (∀ m : ℤ,
        0 < R m ∧ sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ) ∧
      ∃ Qstar : Coeff p →L[ℂ] Coeff p,
        (∀ m k : ℤ, (Qstar (lp.single p k 1)) m =
          sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) ∧
        Tendsto (fun n : ℤ => sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ)
          (Filter.comap Int.natAbs Filter.atTop) (𝓝 Qstar) ∧
        IsCompactOperator (Qstar - (2:ℂ) • ContinuousLinearMap.id ℂ (Coeff p)) ∧
        (∀ h : Coeff p, (∀ k : ℤ, (h k).im = 0) → Qstar h = 0 → h = 0) := by
  obtain ⟨c,R,hcenter,hgeom,Qstar,hentry,hlimit,hcompact,_⟩ :=
    exists_sourcePsiLimitMatrixOperator_normLimit_realKernelGapZeros hp hp1 a φ hφ ha
  refine ⟨c,R,hcenter,hgeom,Qstar,hentry,hlimit,hcompact,?_⟩
  exact sourcePsiLimitMatrixOperator_realKernel_eq_zero
    hp hp1 a φ hφ ha c R hcenter hgeom Qstar hentry

end NLS.ZakharovShabat
