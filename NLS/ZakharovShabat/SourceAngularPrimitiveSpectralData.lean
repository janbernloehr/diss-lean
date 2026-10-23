import NLS.ZakharovShabat.SourcePsiGapRootIsospectral
import NLS.ZakharovShabat.SourceAngularRegularDirichletValue

/-! # Angular primitive transport across actual isospectral sources

The normalized discriminant and psi roots fix the angular integrands.
When a selected Dirichlet point and its full anti-discriminant value also
agree, the sets of normalized primitive values agree, even on a cut.
This is a prerequisite for comparing the actual Dirichlet/sign coordinates;
it does not assume that those coordinates determine the potential.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual normalized psi families agree at isospectral real sources,
including when their complex extension neighborhoods differ. -/
theorem SourcePsiIsolatingComplexExtension.candidate_real_isospectral_agreement
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {s t : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    (D : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (E : SourcePsiIsolatingComplexExtension hp hp1 V t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) (z : ℂ) :
    sourcePsiCandidate n (z,(s n ψ.val : Coeff p)) =
      sourcePsiCandidate n (z,(t n φ.val : Coeff p)) := by
  rw [D.real_isospectral_agreement E φ ψ h n]

theorem sourceAngularRadicand_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (z : ℂ) :
    sourceAngularRadicand hp (z,ψ.val) =
      sourceAngularRadicand hp (z,φ.val) := by
  unfold sourceAngularRadicand
  rw [(mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mp h]

theorem sourceAngularRootSheet_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (w z : ℂ) :
    sourceAngularRootSheet hp w (z,ψ.val) =
      sourceAngularRootSheet hp w (z,φ.val) := by
  simp only [sourceAngularRootSheet, prescribedSquareRoot,
    sourceAngularRadicand_eq_of_isospectral hp hp1 φ ψ h]

theorem sourceAngularRegularSheetDisc_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (c : ℂ) (R : ℝ) (w : ℂ) :
    sourceAngularRegularSheetDisc hp ψ.val c R w =
      sourceAngularRegularSheetDisc hp φ.val c R w := by
  ext z
  simp only [sourceAngularRegularSheetDisc, mem_inter_iff, mem_preimage,
    sourceAngularRootSheetDomain, prescribedSquareRootDomain, mem_ofPred_eq,
    sourceAngularRadicand_eq_of_isospectral hp hp1 φ ψ h]

theorem sourceAngularExteriorPrimitive_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (w : ℂ) (F : ℂ → ℂ) (A : ℂ) :
    sourceAngularExteriorPrimitive hp hp1 ψ.val w F A =
      sourceAngularExteriorPrimitive hp hp1 φ.val w F A := by
  funext z
  simp only [sourceAngularExteriorPrimitive, rootRatioPrimitive,
    sourceCanonicalRoot_eq_of_isospectral hp hp1 φ ψ h,
    sourceAngularRootSheet_eq_of_isospectral hp hp1 φ ψ h]

/-- Equality of the numerators at the two sources suffices to preserve
all exterior and sheet primitive conditions in both directions. -/
theorem sourceAngularSheetPrimitiveData_isospectral_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ.val : Coeff p)) =
      sourcePsiCandidate n (z,(t n φ.val : Coeff p)))
    (c : ℂ) (R : ℝ) (w : ℂ) (F : ℂ → ℂ) (A : ℂ) (E : ℂ → ℂ) :
    SourceAngularSheetPrimitiveData hp hp1 n m s ψ.val c R w F A E ↔
      SourceAngularSheetPrimitiveData hp hp1 n m t
        φ.val c R w F A E := by
  have hseg := sourcePeriodicSegment_eq_of_isospectral hp hp1 φ ψ h m
  have hends := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val) (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  have hdisc := sourceAngularRegularSheetDisc_eq_of_isospectral hp hp1 φ ψ h c R w
  have hext := sourceAngularExteriorPrimitive_eq_of_isospectral hp hp1 φ ψ h w F A
  have hi : ∀ z, sourceAngularIntegrand n s
      (fun u => sourceCanonicalRoot hp hp1 u.2 u.1) (z,ψ.val) =
      sourceAngularIntegrand n t (fun u => sourceCanonicalRoot hp hp1 u.2 u.1)
        (z,φ.val) := by
    intro z
    simp only [sourceAngularIntegrand, hnum,
      sourceCanonicalRoot_eq_of_isospectral hp hp1 φ ψ h]
  have hs : ∀ z, sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ.val) =
      sourceAngularIntegrand n t (sourceAngularRootSheet hp w)
        (z,φ.val) := by
    intro z
    simp only [sourceAngularIntegrand, hnum, sourceAngularRootSheet_eq_of_isospectral hp hp1 φ ψ h]
  constructor <;> intro D
  · exact ⟨by simpa only [hseg, hi] using D.hasDerivAt_exterior,
      by simpa only [hseg, hends.1] using D.tendsto_left_exterior,
      by simpa only [hdisc] using D.analytic_sheet,
      by simpa only [hdisc, hs] using D.hasDerivAt_sheet,
      by simpa only [hdisc, hends.1] using D.tendsto_left_sheet,
      by simpa only [hdisc, hends.2] using D.tendsto_right_sheet,
      by simpa only [hdisc, hseg, hext] using D.eqOn_exterior⟩
  · exact ⟨by simpa only [hseg, hi] using D.hasDerivAt_exterior,
      by simpa only [hseg, hends.1] using D.tendsto_left_exterior,
      by simpa only [hdisc] using D.analytic_sheet,
      by simpa only [hdisc, hs] using D.hasDerivAt_sheet,
      by simpa only [hdisc, hends.1] using D.tendsto_left_sheet,
      by simpa only [hdisc, hends.2] using D.tendsto_right_sheet,
      by simpa only [hdisc, hseg, hext] using D.eqOn_exterior⟩

/-- The Dirichlet terminal, its actual anti-discriminant normalization,
and the normalized primitive data are preserved together. -/
theorem sourceAngularDirichletPrimitiveData_isospectral_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ.val : Coeff p)) =
      sourcePsiCandidate n (z,(t n φ.val : Coeff p)))
    (hmu : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val m =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m)
    (ha : sourceAntiDiscriminantCandidate hp hp1 ψ.val
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val m) =
      sourceAntiDiscriminantCandidate hp hp1 φ.val (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m))
    (c : ℂ) (R : ℝ) (F : ℂ → ℂ) (A : ℂ) (E : ℂ → ℂ) :
    SourceAngularDirichletPrimitiveData hp hp1 n m s ψ.val c R F A E ↔
      SourceAngularDirichletPrimitiveData hp hp1 n m t
        φ.val c R F A E := by
  have hseg := sourcePeriodicSegment_eq_of_isospectral hp hp1 φ ψ h m
  have ha' : sourceAntiDiscriminantCandidate hp hp1 ψ.val
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m) =
      sourceAntiDiscriminantCandidate hp hp1 φ.val
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m) := by
    simpa only [hmu] using ha
  have hprim := sourceAngularSheetPrimitiveData_isospectral_iff hp hp1 φ ψ h n m s t hnum c R
    (sourceAntiDiscriminantCandidate hp hp1 ψ.val
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val m)) F A E
  constructor <;> intro D
  · exact ⟨by simpa only [hseg] using D.gap_enclosed,
      by simpa only [hmu, ha'] using D.root_ne_zero,
      by simpa only [hmu, ha'] using hprim.mp D.primitive,
      by simpa only [sourceAngularRegularSheetDisc_eq_of_isospectral hp hp1 φ ψ h, hmu, ha']
        using D.terminal_mem,
      by simpa only [sourceAngularRootSheet_eq_of_isospectral hp hp1 φ ψ h, hmu, ha']
        using D.terminal_sheet_value⟩
  · refine ⟨by simpa only [hseg] using D.gap_enclosed,
      by simpa only [hmu, ha'] using D.root_ne_zero, ?_,
      by simpa only [sourceAngularRegularSheetDisc_eq_of_isospectral hp hp1 φ ψ h, hmu, ha']
        using D.terminal_mem,
      by simpa only [sourceAngularRootSheet_eq_of_isospectral hp hp1 φ ψ h, hmu, ha']
        using D.terminal_sheet_value⟩
    apply hprim.mpr
    simpa only [hmu, ha'] using D.primitive

/-- Equality of the full sets of normalized regular terminal values;
this transports actual witnesses, including when the terminal is on a cut. -/
theorem sourceAngularRegularDirichletValues_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ.val : Coeff p)) =
      sourcePsiCandidate n (z,(t n φ.val : Coeff p)))
    (hmu : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val m =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m)
    (ha : sourceAntiDiscriminantCandidate hp hp1 ψ.val
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val m) =
      sourceAntiDiscriminantCandidate hp hp1 φ.val (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m)) :
    sourceAngularRegularDirichletValues hp hp1 n m s ψ.val =
      sourceAngularRegularDirichletValues hp hp1 n m t φ.val := by
  ext b
  simp only [sourceAngularRegularDirichletValues, mem_ofPred_eq,
    sourceAngularDirichletPrimitiveData_isospectral_iff hp hp1 φ ψ h n m s t hnum hmu ha, hmu]

end NLS.ZakharovShabat
