import NLS.ZakharovShabat.SourcePsiFullProductGapZeros
import NLS.ZakharovShabat.SourcePsiLimitOperatorContour

/-!
# Full gap-zero sequences from the actual limit operator's kernel

At real gap-contained root data, a real direction in the limit
operator's kernel has a zero of its full product variation in every
periodic gap. Choosing these zeros gives an `ℓᵖ` displaced spectral
sequence without an omitted index. The existence theorem retains the
same real-centered contours, norm limit, and compact correction.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real direction in the bounded contour-limit operator's kernel
gives one simultaneous, gap-contained `ℓᵖ` zero sequence for the full
entire variation. No index is omitted. -/
theorem exists_sourcePsiLimitMatrixOperator_realKernel_gapZero_sequence
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
    (h : Coeff p) (hreal : ∀ k : ℤ, (h k).im = 0) (hkernel : Qstar h = 0) :
    ∃ ρ : ℤ → ℂ, Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p ∧
      ∀ m : ℤ, ρ m ∈ sourcePeriodicSegment hp hp1 φ m ∧
        sourcePsiFullProductVariation a h (ρ m) = 0 := by
  classical
  have hcontours := (sourcePsiLimitMatrixOperator_kernel_iff_fullProductContours_zero
    hp hp1 a φ hφ ha c R (fun m => (hgeom m).1.le)
    (fun m => (hgeom m).2.2.2) Qstar hentry h).mp hkernel
  have hroots (j : ℤ) : (displacedRoots a j).im = 0 :=
    sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ hφ j
      (displacedRoots a j) (ha j)
  have hgap (m : ℤ) : ∃ μ ∈ sourcePeriodicSegment hp hp1 φ m,
      sourcePsiFullProductVariation a h μ = 0 := by
    obtain ⟨x,hx⟩ : ∃ x : ℝ, c m = (x:ℂ) := by
      refine ⟨(c m).re,?_⟩
      apply Complex.ext
      · simp
      · simpa using hcenter m
    have hs : sourcePeriodicSegment hp hp1 φ m ⊆ ball (x:ℂ) (R m) := by
      simpa only [hx] using (hgeom m).2.1
    have hd : closedBall (x:ℂ) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m := by
      simpa only [hx] using (hgeom m).2.2.1
    have hc : sphere (x:ℂ) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ := by
      simpa only [hx] using (hgeom m).2.2.2
    have hz : (∮ z in C((x:ℂ),R m), sourcePsiFullProductVariation a h z /
        sourceCanonicalRoot hp hp1 φ z) = 0 := by
      simpa only [hx] using hcontours m
    exact exists_sourcePsiFullProductVariation_zero_on_realGap
      hp hp1 φ hφ m a h hroots hreal x (R m) (hgeom m).1 hs hd hc hz
  choose ρ hρ using hgap
  exact ⟨ρ,memℓp_sourcePeriodicSegment_samples hp hp1 φ ρ (fun m => (hρ m).1),hρ⟩

/-- The actual norm-limit operator is a compact perturbation of `2I`
on real-centered contours, and every real kernel direction has a full
gap-zero sequence for its entire product variation. -/
theorem exists_sourcePsiLimitMatrixOperator_normLimit_realKernelGapZeros
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
        IsCompactOperator (Qstar - (2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff p)) ∧
        (∀ h : Coeff p, (∀ k : ℤ, (h k).im = 0) → Qstar h = 0 →
          ∃ ρ : ℤ → ℂ, Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p ∧
            ∀ m : ℤ, ρ m ∈ sourcePeriodicSegment hp hp1 φ m ∧
              sourcePsiFullProductVariation a h (ρ m) = 0) := by
  obtain ⟨c,R,hcenter,hgeom,Qstar,_,_,_,_,hentry,hlimit,hcompact,_,_⟩ :=
    exists_sourcePsiLimitMatrixOperator_normLimit_compact_contour_realCentered
      hp hp1 a φ hφ ha
  refine ⟨c,R,hcenter,hgeom,Qstar,hentry,hlimit,hcompact,?_⟩
  exact exists_sourcePsiLimitMatrixOperator_realKernel_gapZero_sequence
    hp hp1 a φ hφ ha c R hcenter hgeom Qstar hentry

end NLS.ZakharovShabat
