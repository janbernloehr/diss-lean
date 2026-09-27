import NLS.ZakharovShabat.SourceNormalizedActionCollapsedCircleValue

/-!
# A chart-independent differentiable normalized action

The existing piecewise normalized-action function is defined on the
entire complex source space. Its value at a zero gap was previously
specified from a real cosine limit. The fixed-circle Cauchy formula
now shows that this same function equals a complex-differentiable
contour candidate on a full neighborhood of every real-type source.
-/

noncomputable section
open Set Metric Complex Filter
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The chart-independent complex normalized action. The historical
piecewise definition was already meaningful for complex sources;
the theorems below establish its local complex regularity. -/
abbrev sourceNormalizedActionComplexExtension
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) : CoeffPair p → ℂ :=
  sourceNormalizedActionRealExtension hp hp1 n

/-- The piecewise normalized action is complex Fréchet differentiable
on a neighborhood of every real-type potential, and its product with
the squared gap is the glued indexed action there. -/
theorem exists_local_sourceNormalizedActionComplexExtension_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      DifferentiableOn ℂ (sourceNormalizedActionComplexExtension hp hp1 n) U ∧
      ∀ ψ ∈ U,
        sourceComplexAction hp hp1 n ψ =
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
            sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  obtain ⟨U,hUopen,hφU,c,R,_,hdiff,hdata⟩ :=
    exists_local_sourceNormalizedActionCircleCandidate_eq_realExtension
      hp hp1 φ hφ n
  let A := sourceNormalizedActionCircleCandidate hp hp1 n c R
  let F := sourceNormalizedActionComplexExtension hp hp1 n
  have heq : EqOn A F U := fun ψ hψ => (hdata ψ hψ).2.2
  have hFdiff : DifferentiableOn ℂ F U := by
    intro ψ hψ
    have hlocal : F =ᶠ[𝓝 ψ] A := by
      filter_upwards [hUopen.mem_nhds hψ] with χ hχ
      exact (heq hχ).symm
    have hA : DifferentiableAt ℂ A ψ :=
      (hdiff ψ hψ).differentiableAt (hUopen.mem_nhds hψ)
    exact (hA.congr_of_eventuallyEq hlocal).differentiableWithinAt
  refine ⟨U,hUopen,hφU,hFdiff,?_⟩
  intro ψ hψ
  calc
    sourceComplexAction hp hp1 n ψ =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * A ψ :=
      (hdata ψ hψ).1
    _ = (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * F ψ :=
      congrArg ((sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * ·) (heq hψ)

/-- In particular, the chart-independent normalized action has a
complex Fréchet derivative at every real-type potential, including
those with collapsed periodic gaps. -/
theorem differentiableAt_sourceNormalizedActionComplexExtension_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    DifferentiableAt ℂ (sourceNormalizedActionComplexExtension hp hp1 n) φ := by
  obtain ⟨U,hUopen,hφU,hdiff,_⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_differentiableOn
      hp hp1 φ hφ n
  exact (hdiff φ hφU).differentiableAt (hUopen.mem_nhds hφU)

/-- Every complex affine source line through a real-type potential
sees a one-variable analytic normalized action, with no noncollapsed
gap hypothesis. -/
theorem analyticAt_sourceNormalizedActionComplexExtension_alongLine_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (h : CoeffPair p) :
    AnalyticAt ℂ (fun t : ℂ =>
      sourceNormalizedActionComplexExtension hp hp1 n (φ+t•h)) 0 := by
  obtain ⟨U,hUopen,hφU,hdiff,_⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_differentiableOn
      hp hp1 φ hφ n
  let a : ℂ → CoeffPair p := fun t => φ+t•h
  have ha : Differentiable ℂ a := by
    dsimp [a]
    fun_prop
  let V : Set ℂ := a ⁻¹' U
  have hVopen : IsOpen V := hUopen.preimage ha.continuous
  have h0 : (0:ℂ) ∈ V := by simpa [V,a] using hφU
  have hline : DifferentiableOn ℂ
      (fun t : ℂ => sourceNormalizedActionComplexExtension hp hp1 n (a t)) V := by
    intro t ht
    exact (((hdiff (a t) ht).differentiableAt (hUopen.mem_nhds ht)).comp t
      (ha t)).differentiableWithinAt
  exact hline.analyticAt (hVopen.mem_nhds h0)

/-- For each fixed spectral index, one open complex source domain
contains the entire real-type locus. The chart-independent quotient
is differentiable there and exactly factors the glued action. -/
theorem exists_global_sourceNormalizedActionComplexExtension_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      W ⊆ sourceComplexActionDomain hp hp1 n ∧
      DifferentiableOn ℂ (sourceNormalizedActionComplexExtension hp hp1 n) W ∧
      ∀ ψ ∈ W,
        sourceComplexAction hp hp1 n ψ =
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
            sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  let F := sourceNormalizedActionComplexExtension hp hp1 n
  let P : Set (CoeffPair p) := {ψ | ∃ U : Set (CoeffPair p),
    IsOpen U ∧ ψ ∈ U ∧ DifferentiableOn ℂ F U ∧
      ∀ χ ∈ U,
        sourceComplexAction hp hp1 n χ =
          (sourcePeriodicGapDisplacement hp hp1 χ n)^2 * F χ}
  have hPopen : IsOpen P := by
    apply isOpen_iff_mem_nhds.mpr
    intro ψ hψ
    obtain ⟨U,hUopen,hψU,hdiff,hfactor⟩ := hψ
    exact Filter.mem_of_superset (hUopen.mem_nhds hψU)
      (fun χ hχ => ⟨U,hUopen,hχ,hdiff,hfactor⟩)
  have hrealP : realTypeSourceLocus p ⊆ P := by
    intro φ hφ
    obtain ⟨U,hUopen,hφU,hdiff,hfactor⟩ :=
      exists_local_sourceNormalizedActionComplexExtension_differentiableOn
        hp hp1 φ hφ n
    exact ⟨U,hUopen,hφU,hdiff,hfactor⟩
  let W := P ∩ sourceComplexActionDomain hp hp1 n
  have hWopen : IsOpen W :=
    hPopen.inter (isOpen_sourceComplexActionDomain hp hp1 n)
  have hrealW : realTypeSourceLocus p ⊆ W := by
    intro φ hφ
    exact ⟨hrealP hφ,
      realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 n hφ⟩
  refine ⟨W,hWopen,hrealW,inter_subset_right,?_,?_⟩
  · intro ψ hψ
    obtain ⟨U,hUopen,hψU,hdiff,_⟩ := hψ.1
    exact (((hdiff ψ hψU).differentiableAt
      (hUopen.mem_nhds hψU))).differentiableWithinAt
  · intro ψ hψ
    obtain ⟨U,_,hψU,_,hfactor⟩ := hψ.1
    exact hfactor ψ hψU

end NLS.ZakharovShabat
