import NLS.ZakharovShabat.SourceCanonicalRootExponent
import NLS.ZakharovShabat.SourceAngularRegularDirichletValue

/-! # Exponent compatibility of normalized angular primitives

At a fixed source, all spectral sheets and normalizations are unchanged
by coefficient-preserving exponent inclusion. If the psi numerators
agree at that source, exactly the same primitive witnesses work in
both spaces. No source-neighborhood transport is assumed.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem sourceAngularRadicand_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p ≤ q) (ψ : CoeffPair p) (z : ℂ) :
    sourceAngularRadicand hp (z,ψ) =
      sourceAngularRadicand hq (z,CoeffPair.exponentInclusion hpq ψ) := by
  unfold sourceAngularRadicand
  rw [sourceDiscriminant_exponent hp hq hpq ψ z]

theorem sourceAngularRootSheet_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p ≤ q) (ψ : CoeffPair p) (w z : ℂ) :
    sourceAngularRootSheet hp w (z,ψ) =
      sourceAngularRootSheet hq w (z,CoeffPair.exponentInclusion hpq ψ) := by
  simp only [sourceAngularRootSheet, prescribedSquareRoot,
    sourceAngularRadicand_exponent hp hq hpq ψ]

theorem sourceAngularRegularSheetDisc_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p ≤ q)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (w : ℂ) :
    sourceAngularRegularSheetDisc hp ψ c R w =
      sourceAngularRegularSheetDisc hq (CoeffPair.exponentInclusion hpq ψ) c R w := by
  ext z
  simp only [sourceAngularRegularSheetDisc, mem_inter_iff, mem_preimage,
    sourceAngularRootSheetDomain, prescribedSquareRootDomain, mem_ofPred_eq,
    sourceAngularRadicand_exponent hp hq hpq ψ]

theorem sourceAngularExteriorPrimitive_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (ψ : CoeffPair p) (w : ℂ) (F : ℂ → ℂ) (A : ℂ) :
    sourceAngularExteriorPrimitive hp hp1 ψ w F A =
      sourceAngularExteriorPrimitive hq hq1 (CoeffPair.exponentInclusion hpq ψ) w F A := by
  funext z
  simp only [sourceAngularExteriorPrimitive, rootRatioPrimitive,
    sourceCanonicalRoot_exponent hp hq hp1 hq1 hpq ψ,
    sourceAngularRootSheet_exponent hp hq hpq ψ]

/-- Equality of the numerator at the fixed source suffices to preserve
all exterior and sheet primitive conditions in both directions. -/
theorem sourceAngularSheetPrimitiveData_exponent_iff
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair q → DeletedCoeff q k) (ψ : CoeffPair p)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q)))
    (c : ℂ) (R : ℝ) (w : ℂ) (F : ℂ → ℂ) (A : ℂ) (E : ℂ → ℂ) :
    SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E ↔
      SourceAngularSheetPrimitiveData hq hq1 n m t
        (CoeffPair.exponentInclusion hpq ψ) c R w F A E := by
  have hseg := sourcePeriodicSegment_exponent hp hq hp1 hq1 hpq ψ m
  have hends := canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq ψ
  have hdisc := sourceAngularRegularSheetDisc_exponent hp hq hpq ψ c R w
  have hext := sourceAngularExteriorPrimitive_exponent hp hq hp1 hq1 hpq ψ w F A
  have hi : ∀ z, sourceAngularIntegrand n s
      (fun u => sourceCanonicalRoot hp hp1 u.2 u.1) (z,ψ) =
      sourceAngularIntegrand n t (fun u => sourceCanonicalRoot hq hq1 u.2 u.1)
        (z,CoeffPair.exponentInclusion hpq ψ) := by
    intro z
    simp only [sourceAngularIntegrand, hnum,
      sourceCanonicalRoot_exponent hp hq hp1 hq1 hpq ψ]
  have hs : ∀ z, sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ) =
      sourceAngularIntegrand n t (sourceAngularRootSheet hq w)
        (z,CoeffPair.exponentInclusion hpq ψ) := by
    intro z
    simp only [sourceAngularIntegrand, hnum, sourceAngularRootSheet_exponent hp hq hpq ψ]
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
theorem sourceAngularDirichletPrimitiveData_exponent_iff
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair q → DeletedCoeff q k) (ψ : CoeffPair p)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q)))
    (c : ℂ) (R : ℝ) (F : ℂ → ℂ) (A : ℂ) (E : ℂ → ℂ) :
    SourceAngularDirichletPrimitiveData hp hp1 n m s ψ c R F A E ↔
      SourceAngularDirichletPrimitiveData hq hq1 n m t
        (CoeffPair.exponentInclusion hpq ψ) c R F A E := by
  have hseg := sourcePeriodicSegment_exponent hp hq hp1 hq1 hpq ψ m
  have hmu := canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 hpq .dirichlet ψ
  have ha := sourceAntiDiscriminantCandidate_exponent hp hq hp1 hq1 hpq ψ
  have hprim := sourceAngularSheetPrimitiveData_exponent_iff hp hq hp1 hq1 hpq n m s t ψ hnum c R
    (sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)) F A E
  constructor <;> intro D
  · exact ⟨by simpa only [hseg] using D.gap_enclosed,
      by simpa only [hmu, ha] using D.root_ne_zero,
      by simpa only [hmu, ha] using hprim.mp D.primitive,
      by simpa only [sourceAngularRegularSheetDisc_exponent hp hq hpq ψ, hmu, ha]
        using D.terminal_mem,
      by simpa only [sourceAngularRootSheet_exponent hp hq hpq ψ, hmu, ha]
        using D.terminal_sheet_value⟩
  · refine ⟨by simpa only [hseg] using D.gap_enclosed,
      by simpa only [hmu, ha] using D.root_ne_zero, ?_,
      by simpa only [sourceAngularRegularSheetDisc_exponent hp hq hpq ψ, hmu, ha]
        using D.terminal_mem,
      by simpa only [sourceAngularRootSheet_exponent hp hq hpq ψ, hmu, ha]
        using D.terminal_sheet_value⟩
    apply hprim.mpr
    simpa only [hmu, ha] using D.primitive

/-- Equality of the full sets of normalized regular terminal values;
this transports actual witnesses, including when the terminal is on a cut. -/
theorem sourceAngularRegularDirichletValues_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair q → DeletedCoeff q k) (ψ : CoeffPair p)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q))) :
    sourceAngularRegularDirichletValues hp hp1 n m s ψ =
      sourceAngularRegularDirichletValues hq hq1 n m t (CoeffPair.exponentInclusion hpq ψ) := by
  ext b
  simp only [sourceAngularRegularDirichletValues, mem_ofPred_eq,
    sourceAngularDirichletPrimitiveData_exponent_iff hp hq hp1 hq1 hpq n m s t ψ hnum,
    canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 hpq .dirichlet ψ]

end NLS.ZakharovShabat
