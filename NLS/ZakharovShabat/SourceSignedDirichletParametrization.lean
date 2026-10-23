import NLS.ZakharovShabat.SourceDirichletRealSheetCoordinates
import NLS.ZakharovShabat.SourceDirichletSheetParametrization

/-! # The literal signed Dirichlet parametrization of actual Hilbert isospectral sets

The actual terminal homeomorphism, followed by the explicit signed-sheet
homeomorphisms, is exactly the Dirichlet eigenvalue/sign map. The target
uses the quotient topology of two interval branches identified at endpoints.
Every admissible literal prescription has a unique actual realization,
without a finite-gap hypothesis.
-/
noncomputable section
open Set Complex NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceSignedDirichletParametrization_factTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The actual eigenvalue/sign map is a homeomorphism onto the product of signed gaps,
with the branch-quotient topology at each coordinate. -/
def sourceHilbertSignedDirichletHomeomorph (φ : realTypeSourceSubmodule 2) :
    sourceIsospectralSet (by simp) φ ≃ₜ
      ((n : ℤ) → SourceSignedDirichletSheet (by simp) (by norm_num) φ n) :=
  (sourceHilbertDirichletSheetHomeomorph φ).trans
    (Homeomorph.piCongrRight (fun n => sourceDirichletSignedSheetHomeomorph (by simp) (by norm_num) φ n))

@[simp] theorem sourceHilbertSignedDirichletHomeomorph_base (φ : realTypeSourceSubmodule 2)
    (ψ : sourceIsospectralSet (by simp) φ) (n : ℤ) :
    (sourceHilbertSignedDirichletHomeomorph φ ψ n).base =
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ.val.val n).re := rfl

@[simp] theorem sourceHilbertSignedDirichletHomeomorph_sign (φ : realTypeSourceSubmodule 2)
    (ψ : sourceIsospectralSet (by simp) φ) (n : ℤ) :
    (sourceHilbertSignedDirichletHomeomorph φ ψ n).sign =
      sourceDirichletSign (by simp) (by norm_num) ψ.val n := rfl

/-- Prescribed real gap points and literal signs have an actual isospectral realization.
Admissibility means precisely that the zero sign occurs at the two endpoints. -/
theorem exists_isospectral_source_with_signed_dirichletData
    (φ : realTypeSourceSubmodule 2) (μ : ℤ → ℝ) (σ : ℤ → SignType)
    (hμ : ∀ n, μ n ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re)
    (hσ : ∀ n, σ n = 0 ↔
      μ n = (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re ∨
      μ n = (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re) :
    ∃ ψ : realTypeSourceSubmodule 2,
      ψ ∈ sourceIsospectralSet (by simp) φ ∧ ∀ n,
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ.val n = (μ n : ℂ) ∧
      sourceDirichletSign (by simp) (by norm_num) ψ n = σ n := by
  let z : (n : ℤ) → SourceSignedDirichletSheet (by simp) (by norm_num) φ n := fun n => {
    base := μ n
    sign := σ n
    base_mem := hμ n
    height_nonneg := sourceDirichletSheetHeight_nonneg (by simp) (by norm_num) φ n (μ n) (hμ n)
    sign_zero_iff := (hσ n).trans (sourceDirichletSheetHeight_zero_iff (by simp) (by norm_num) φ n (μ n) (hμ n)).symm }
  obtain ⟨ψ,he⟩ := (sourceHilbertSignedDirichletHomeomorph φ).surjective z
  refine ⟨ψ.val,ψ.property,?_⟩
  intro n
  constructor
  · apply Complex.ext
    · exact congrArg RealSignedSheet.base (congrFun he n)
    · exact canonicalPeriodOneBoundaryRoots_im_eq_zero (by simp) (by norm_num) .dirichlet ψ.val.val ψ.val.property n
  · exact congrArg RealSignedSheet.sign (congrFun he n)

/-- Each admissible literal signed prescription has exactly one realization in the
original Hilbert isospectral set, including all algebraic multiplicities. -/
theorem existsUnique_isospectral_source_with_signed_dirichletData
    (φ : realTypeSourceSubmodule 2) (μ : ℤ → ℝ) (σ : ℤ → SignType)
    (hμ : ∀ n, μ n ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re)
    (hσ : ∀ n, σ n = 0 ↔
      μ n = (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re ∨
      μ n = (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re) :
    ∃! ψ : sourceIsospectralSet (by simp) φ, ∀ n,
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ.val.val n = (μ n : ℂ) ∧
      sourceDirichletSign (by simp) (by norm_num) ψ.val n = σ n := by
  obtain ⟨ψ,hψ,he⟩ := exists_isospectral_source_with_signed_dirichletData φ μ σ hμ hσ
  refine ⟨⟨ψ,hψ⟩,he,?_⟩
  intro χ hχ
  apply Subtype.ext
  apply sourceSignedDirichletData_injOn_isospectralSet (by simp) (by norm_num) φ χ.property hψ
  funext n
  exact Prod.ext ((hχ n).1.trans (he n).1.symm) ((hχ n).2.trans (he n).2.symm)

end NLS.ZakharovShabat
