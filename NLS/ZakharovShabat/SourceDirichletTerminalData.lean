import NLS.ZakharovShabat.SourceDirichletSpectralSheet
import NLS.ZakharovShabat.SourceSignedDirichletUniqueness

/-! # Continuous actual Dirichlet terminal data

Pairing the actual Dirichlet eigenvalue with the full anti-discriminant
retains both branches and joins them at each endpoint. The coordinate map
is continuous, stays on the fixed isospectral sheets, and is injective on
an actual isospectral set by signed Dirichlet uniqueness.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Dirichlet root paired with its full terminal sheet value. -/
def sourceDirichletTerminalData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) : ℤ → ℂ × ℂ := fun n =>
  (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n,
    sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet n φ.val)

/-- Actual terminal data are continuous in the source norm and coordinate product topology. -/
theorem continuous_sourceDirichletTerminalData (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Continuous (sourceDirichletTerminalData hp hp1) := by
  apply continuous_pi
  intro n
  apply continuous_iff_continuousAt.mpr
  intro φ
  exact ((continuousAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property n).comp
    continuous_subtype_val.continuousAt).prodMk
    ((analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType hp hp1 .dirichlet n φ.val φ.property).continuousAt.comp
      continuous_subtype_val.continuousAt)

/-- The entire algebraic sheet, including its endpoint identifications, is fixed by actual isospectrality. -/
theorem sourceDirichletSpectralSheet_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) :
    sourceDirichletSpectralSheet hp hp1 n ψ.val = sourceDirichletSpectralSheet hp hp1 n φ.val := by
  have he := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  have hΔ := (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mp h
  simp only [sourceDirichletSpectralSheet,sourcePeriodicSegment,he.1,he.2,hΔ]

/-- Every coordinate of the actual terminal data lies on the source's fixed algebraic sheet. -/
theorem sourceDirichletTerminalData_mem_sheet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceDirichletTerminalData hp hp1 φ n ∈ sourceDirichletSpectralSheet hp hp1 n φ.val := by
  refine ⟨canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1 .dirichlet φ.val φ.property n,?_⟩
  exact (sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 φ.val n).symm

/-- Terminal data of an actual isospectral source lie on the original source's sheets. -/
theorem sourceDirichletTerminalData_mem_sheet_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) :
    sourceDirichletTerminalData hp hp1 ψ n ∈ sourceDirichletSpectralSheet hp hp1 n φ.val := by
  rw [← sourceDirichletSpectralSheet_eq_of_isospectral hp hp1 φ ψ h n]
  exact sourceDirichletTerminalData_mem_sheet hp hp1 ψ n

/-- Full terminal data separate points of every actual isospectral set. -/
theorem sourceDirichletTerminalData_injOn_isospectralSet
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) :
    InjOn (sourceDirichletTerminalData hp hp1) (sourceIsospectralSet hp φ) := by
  intro ψ hψ χ hχ he
  apply sourceSignedDirichletData_injOn_isospectralSet hp hp1 φ hψ hχ
  funext n
  apply Prod.ext
  · exact congrArg (fun z : ℂ × ℂ => z.1) (congrFun he n)
  · exact congrArg (fun z : ℂ × ℂ => SignType.sign z.2.re) (congrFun he n)

end NLS.ZakharovShabat
