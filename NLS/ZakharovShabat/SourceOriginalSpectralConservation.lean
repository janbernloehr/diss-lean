import NLS.ZakharovShabat.SourceSection22Original
import NLS.ZakharovShabat.SourceActionIsospectralAllExponents

/-! # Spectral conservation along original global solutions

This implements the original dynamics statements in the introduction, printed p. 9.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every original global ordinary solution preserves each original spectral action. -/
theorem sourceComplexAction_of_isOrdinaryNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsOrdinaryNLSSolutionOn univ φ γ) (τ : ℝ) (n : ℤ) :
    sourceComplexAction hp hp1 n (γ τ).val = sourceComplexAction hp hp1 n φ.val := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original hp hp1
  have he := hγ.eqOn_inter (Q.global_physical_solutions hp2 φ).2 hp hp1
    ⟨mem_univ τ,mem_univ τ⟩
  rw [he]
  exact A.hamiltonianOrdinarySourceFlow_action D.complex hp2 φ τ n

/-- The same original action conservation holds for every global renormalized solution. -/
theorem sourceComplexAction_of_isRenormalizedNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsRenormalizedNLSSolutionOn univ φ γ) (τ : ℝ) (n : ℤ) :
    sourceComplexAction hp hp1 n (γ τ).val = sourceComplexAction hp hp1 n φ.val := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original hp hp1
  have he := hγ.eqOn_inter (Q.global_physical_solutions hp2 φ).1 hp hp1
    ⟨mem_univ τ,mem_univ τ⟩
  rw [he]
  exact A.hamiltonianRenormalizedSourceFlow_action D.complex hp2 φ τ n

/-- Original action conservation implies actual periodic isospectrality. -/
theorem sourceIsospectralSet_of_complex_actions (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p)
    (ha : ∀ n : ℤ, sourceComplexAction hp hp1 n ψ.val = sourceComplexAction hp hp1 n φ.val) :
    ψ ∈ sourceIsospectralSet hp φ := by
  rw [sourceIsospectralSet_eq_actionLevelSet_all_exponents hp hp1 φ]
  intro n
  have h := ha n
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n _ ψ.property,
    sourceComplexAction_eq_sourceRealAction hp hp1 n _ φ.property] at h
  exact congrArg Complex.re h

/-- Every global ordinary solution preserves the original periodic spectrum and every algebraic multiplicity. -/
theorem isospectral_of_isOrdinaryNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsOrdinaryNLSSolutionOn univ φ γ) (τ : ℝ) :
    γ τ ∈ sourceIsospectralSet hp φ :=
  sourceIsospectralSet_of_complex_actions hp hp1 φ (γ τ)
    (sourceComplexAction_of_isOrdinaryNLSSolutionOn_univ hp hp1 hp2 hγ τ)

/-- The renormalized physical solution has the same original periodic spectrum and multiplicities. -/
theorem isospectral_of_isRenormalizedNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsRenormalizedNLSSolutionOn univ φ γ) (τ : ℝ) :
    γ τ ∈ sourceIsospectralSet hp φ :=
  sourceIsospectralSet_of_complex_actions hp hp1 φ (γ τ)
    (sourceComplexAction_of_isRenormalizedNLSSolutionOn_univ hp hp1 hp2 hγ τ)

/-- The normalized discriminant itself is conserved at every spectral parameter. -/
theorem discriminant_of_isOrdinaryNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsOrdinaryNLSSolutionOn univ φ γ) (τ : ℝ) :
    canonicalDiscriminant hp (periodOnePotential (γ τ).val) =
      canonicalDiscriminant hp (periodOnePotential φ.val) :=
  (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ (γ τ)).mp
    (isospectral_of_isOrdinaryNLSSolutionOn_univ hp hp1 hp2 hγ τ)

/-- The same normalized discriminant is conserved by the renormalized solution. -/
theorem discriminant_of_isRenormalizedNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsRenormalizedNLSSolutionOn univ φ γ) (τ : ℝ) :
    canonicalDiscriminant hp (periodOnePotential (γ τ).val) =
      canonicalDiscriminant hp (periodOnePotential φ.val) :=
  (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ (γ τ)).mp
    (isospectral_of_isRenormalizedNLSSolutionOn_univ hp hp1 hp2 hγ τ)

end NLS.ZakharovShabat
