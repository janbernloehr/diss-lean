import NLS.ZakharovShabat.ResolventContour
import NLS.FunctionalAnalysis.RectangleIntegral

/-!
# Actual rectangular integrals of the periodic resolvent

These are operator-norm integrals along four oriented straight edges. Boundary
admissibility gives evaluation, domain factorization, compactness, and resolvent
commutation. Cauchy's theorem applies when the whole rectangle is admissible.
Identification with the enclosed algebraic spectral projection is separate.
-/

noncomputable section
open Complex Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Normalized rectangular integral of `(ζ-L)⁻¹`, with opposite corners `z,w`. -/
def resolventRectangleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ) :
    PairSpace p →L[ℂ] PairSpace p :=
  (2 * Real.pi * I : ℂ)⁻¹ • RectangleIntegral.integral (resolvent hp φ) z w

/-- The same four-edge integral with values in the one-derivative domain. -/
def resolventRectangleIntegralToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ) :
    PairSpace p →L[ℂ] Domain p :=
  (2 * Real.pi * I : ℂ)⁻¹ • RectangleIntegral.integral (resolventToDomain hp φ) z w

/-- A resolvent boundary makes all four operator-valued integrals integrable. -/
theorem rectangleIntegrable_resolvent (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    RectangleIntegral.Integrable (resolvent hp φ) z w :=
  RectangleIntegral.integrable_of_continuousOn ((analyticOnNhd_resolvent hp φ).continuousOn.mono hc)

private theorem continuousOn_resolventToDomain_rectangle (hp : p ≠ ⊤) (φ : PairSpace p)
    (z w : ℂ) (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    ContinuousOn (resolventToDomain hp φ) (RectangleIntegral.boundary z w) := by
  intro ζ hζ
  exact ((analyticAt_resolventToDomain hp (φ, ζ) (hc hζ)).comp
    (analyticAt_const.prod analyticAt_id)).continuousAt.continuousWithinAt

/-- The rectangular integral also exists in the stronger domain norm. -/
theorem rectangleIntegrable_resolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    RectangleIntegral.Integrable (resolventToDomain hp φ) z w :=
  RectangleIntegral.integrable_of_continuousOn (continuousOn_resolventToDomain_rectangle hp φ z w hc)

/-- Evaluation commutes with the normalized operator integral. -/
theorem resolventRectangleIntegral_apply (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) (x : PairSpace p) :
    resolventRectangleIntegral hp φ z w x =
      (2 * Real.pi * I : ℂ)⁻¹ • RectangleIntegral.integral (fun ζ => resolvent hp φ ζ x) z w := by
  rw [resolventRectangleIntegral, smul_apply,
    RectangleIntegral.apply (rectangleIntegrable_resolvent hp φ z w hc) x]

/-- The full four-edge operator integral factors through the weighted domain. -/
theorem resolventRectangleIntegral_eq_inclusion (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    resolventRectangleIntegral hp φ z w = domainInclusion.comp (resolventRectangleIntegralToDomain hp φ z w) := by
  apply ContinuousLinearMap.ext
  intro x
  have hi := RectangleIntegral.integrable_of_continuousOn
    ((continuousOn_resolventToDomain_rectangle hp φ z w hc).clm_apply (g := fun _ => x) continuousOn_const)
  rw [resolventRectangleIntegral_apply hp φ z w hc]
  change _ = domainInclusion (resolventRectangleIntegralToDomain hp φ z w x)
  rw [resolventRectangleIntegralToDomain, smul_apply,
    RectangleIntegral.apply (rectangleIntegrable_resolventToDomain hp φ z w hc),
    map_smul, RectangleIntegral.map domainInclusion hi]
  rfl

/-- Compactness follows from the domain factorization, without a pointwise integral definition. -/
theorem isCompactOperator_resolventRectangleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    IsCompactOperator (resolventRectangleIntegral hp φ z w) := by
  have hI : I ∉ freeLattice := notMem_freeLattice_of_im_ne_zero (by simp)
  have heq : (freeResolvent (p := p) I hI).comp (freePencil I) = domainInclusion := by
    apply ContinuousLinearMap.ext
    intro f
    change domainInclusion (freeResolventToDomain I hI (freePencil I f)) = domainInclusion f
    rw [freeResolventToDomain_freePencil]
  rw [resolventRectangleIntegral_eq_inclusion hp φ z w hc, ← heq, ContinuousLinearMap.comp_assoc]
  exact (isCompactOperator_freeResolvent (p := p) I hI).comp_clm _

/-- An admissible filled rectangle contributes zero by Cauchy's theorem. -/
theorem resolventRectangleIntegral_eq_zero_of_rectangle_subset (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hc : uIcc z.re w.re ×ℂ uIcc z.im w.im ⊆ resolventSet hp φ) :
    resolventRectangleIntegral hp φ z w = 0 := by
  rw [resolventRectangleIntegral,
    RectangleIntegral.eq_zero_of_differentiableOn ((analyticOnNhd_resolvent hp φ).differentiableOn.mono hc),
    smul_zero]

/-- Any operator commuting with all boundary resolvents commutes with their rectangular integral. -/
theorem commute_resolventRectangleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) (A : PairSpace p →L[ℂ] PairSpace p)
    (hA : ∀ ζ ∈ RectangleIntegral.boundary z w, Commute A (resolvent hp φ ζ)) :
    Commute A (resolventRectangleIntegral hp φ z w) := by
  apply ContinuousLinearMap.ext
  intro x
  change A (resolventRectangleIntegral hp φ z w x) = resolventRectangleIntegral hp φ z w (A x)
  have hi := RectangleIntegral.integrable_of_continuousOn
    (((analyticOnNhd_resolvent hp φ).continuousOn.mono hc).clm_apply (g := fun _ => x) continuousOn_const)
  rw [resolventRectangleIntegral_apply hp φ z w hc, resolventRectangleIntegral_apply hp φ z w hc,
    map_smul, RectangleIntegral.map A hi]
  congr 1
  exact RectangleIntegral.congr (fun ζ hζ => DFunLike.congr_fun (hA ζ hζ).eq x)

/-- Rectangular contour operators commute with every resolvent of the same potential. -/
theorem resolventRectangleIntegral_commute_resolvent (hp : p ≠ ⊤) (φ : PairSpace p) (z w a : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) (ha : a ∈ resolventSet hp φ) :
    Commute (resolventRectangleIntegral hp φ z w) (resolvent hp φ a) :=
  (commute_resolventRectangleIntegral hp φ z w hc _
    (fun ζ hζ => resolvent_commute hp φ a ζ ha (hc hζ))).symm

/-- The actual rectangular contour commutes with each full algebraic root-space projection. -/
theorem periodicSpectralProjection_commute_rectangle (hp : p ≠ ⊤) (φ : PairSpace p) (z w a : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    Commute (periodicSpectralProjection hp φ a) (resolventRectangleIntegral hp φ z w) :=
  commute_resolventRectangleIntegral hp φ z w hc _
    (fun ζ hζ => periodicSpectralProjection_commute_resolvent hp φ a ζ (hc hζ))

/-- Moving a horizontal edge through a filled resolvent strip preserves the integral. -/
theorem resolventRectangleIntegral_eq_of_horizontal_strip (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ) (c : ℝ)
    (hc : RectangleIntegral.boundary z ⟨w.re, c⟩ ⊆ resolventSet hp φ)
    (hs : uIcc z.re w.re ×ℂ uIcc c w.im ⊆ resolventSet hp φ) :
    resolventRectangleIntegral hp φ z w = resolventRectangleIntegral hp φ z ⟨w.re, c⟩ := by
  unfold resolventRectangleIntegral
  rw [RectangleIntegral.eq_of_horizontal_strip c (rectangleIntegrable_resolvent hp φ _ _ hc)
    ((analyticOnNhd_resolvent hp φ).differentiableOn.mono hs)]

/-- Moving a vertical edge through a filled resolvent strip preserves the integral. -/
theorem resolventRectangleIntegral_eq_of_vertical_strip (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ) (c : ℝ)
    (hc : RectangleIntegral.boundary z ⟨c, w.im⟩ ⊆ resolventSet hp φ)
    (hs : uIcc c w.re ×ℂ uIcc z.im w.im ⊆ resolventSet hp φ) :
    resolventRectangleIntegral hp φ z w = resolventRectangleIntegral hp φ z ⟨c, w.im⟩ := by
  unfold resolventRectangleIntegral
  rw [RectangleIntegral.eq_of_vertical_strip c (rectangleIntegrable_resolvent hp φ _ _ hc)
    ((analyticOnNhd_resolvent hp φ).differentiableOn.mono hs)]

end NLS.ZakharovShabat
