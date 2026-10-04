import NLS.ZakharovShabat.SourcePsiGapRootExponent
import NLS.ZakharovShabat.SourceIsospectralSet

/-! # Isospectral invariance of the normalized psi roots

Equal periodic spectra with multiplicities preserve the signed gap
geometry and the literal contour equations. Uniqueness of the actual
gap-contained solution therefore identifies the normalized psi roots.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Signed periodic segments agree for isospectral real sources. -/
theorem sourcePeriodicSegment_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) :
    sourcePeriodicSegment hp hp1 ψ.val n = sourcePeriodicSegment hp hp1 φ.val n := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val) (periodOnePotential_mem _) (periodOnePotential_mem _)
    h.1 h.2
  unfold sourcePeriodicSegment
  rw [hl,hr]

theorem sourceCanonicalRootDomain_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) :
    sourceCanonicalRootDomain hp hp1 ψ.val = sourceCanonicalRootDomain hp hp1 φ.val := by
  simp only [sourceCanonicalRootDomain,sourcePeriodicSegment_eq_of_isospectral hp hp1 φ ψ h]

theorem sourceStandardRootOmittedDomain_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) :
    sourceStandardRootOmittedDomain hp hp1 ψ.val n = sourceStandardRootOmittedDomain hp hp1 φ.val n := by
  simp only [sourceStandardRootOmittedDomain,sourcePeriodicSegment_eq_of_isospectral hp hp1 φ ψ h]

/-- The actual normalized contour equation is an isospectral invariant. -/
theorem sourcePsiEquationCoordinate_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n m : ℤ) (a : Coeff p) (c : ℂ) (R : ℝ) :
    sourcePsiEquationCoordinate hp hp1 n m a ψ.val c R =
      sourcePsiEquationCoordinate hp hp1 n m a φ.val c R := by
  simp only [sourcePsiEquationCoordinate,sourcePsiContour,sourcePsiContourIntegrandJoint,
    sourceCanonicalRoot_eq_of_isospectral hp hp1 φ ψ h]

/-- Isospectral transport preserves an actual gap-contained zero solution. -/
theorem SourcePsiGapSolution.of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n : ℤ) (a : DeletedCoeff p n) (ha : SourcePsiGapSolution hp hp1 n ψ.val a) :
    SourcePsiGapSolution hp hp1 n φ.val a := by
  obtain ⟨hgap,c,R,hcenter,hgeom,hcoord,hzero⟩ := ha
  have heq (m : ℤ) : sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) φ.val (c m) (R m) = 0 := by
    rw [← sourcePsiEquationCoordinate_eq_of_isospectral hp hp1 φ ψ h,
      ← hcoord m,hzero]
    rfl
  have hex : ∃ F : DeletedCoeff p n, ∀ m : ℤ, (F : Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) φ.val (c m) (R m) :=
    ⟨0,fun m => (heq m).symm⟩
  have hc := sourcePsiSelectedEquationSequence_apply_of_exists hp hp1 n c R a φ.val hex
  refine ⟨?_,c,R,hcenter,?_,hc,?_⟩
  · intro m hm
    rw [← sourcePeriodicSegment_eq_of_isospectral hp hp1 φ ψ h m]
    exact hgap m hm
  · intro m
    rw [← sourcePeriodicSegment_eq_of_isospectral hp hp1 φ ψ h m,
      ← sourceStandardRootOmittedDomain_eq_of_isospectral hp hp1 φ ψ h m]
    exact hgeom m
  · apply Subtype.ext
    ext m
    rw [hc m]
    exact heq m

/-- The selected normalized real psi roots depend only on the spectrum. -/
theorem sourcePsiGapRoot_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) :
    sourcePsiGapRoot hp hp1 n ψ = sourcePsiGapRoot hp hp1 n φ := by
  apply SourcePsiGapSolution.eq_sourcePsiGapRoot hp hp1 n
  exact (sourcePsiGapRoot_solution hp hp1 n ψ).of_isospectral hp hp1 φ ψ h n _

/-- Independent compatible complex extensions have the same values
at isospectral real sources. -/
theorem SourcePsiIsolatingComplexExtension.real_isospectral_agreement
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (E : SourcePsiIsolatingComplexExtension hp hp1 V t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) :
    s n ψ.val = t n φ.val := by
  rw [D.real_agreement n ψ,E.real_agreement n φ]
  exact sourcePsiGapRoot_eq_of_isospectral hp hp1 φ ψ h n

end NLS.ZakharovShabat
