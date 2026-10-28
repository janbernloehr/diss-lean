import NLS.ZakharovShabat.SourceOriginalSpectralConservation

/-! # The isospectral decomposition in the opening of Section 7

The original spectral sets, including algebraic multiplicities, partition
the real source space. Every global ordinary NLS solution remains in its
initial class. The conservation input is the proved physical solution
theorem; no independent Lax-pair identity is asserted here.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every real source belongs to its original periodic spectral class. -/
@[simp] theorem mem_sourceIsospectralSet_self (hp : p ≠ ⊤)
    (φ : realTypeSourceSubmodule p) : φ ∈ sourceIsospectralSet hp φ :=
  ⟨rfl, fun _ => rfl⟩

/-- Choosing another member as the base leaves the whole spectral class unchanged. -/
theorem sourceIsospectralSet_eq_of_mem (hp : p ≠ ⊤)
    {φ ψ : realTypeSourceSubmodule p} (hψ : ψ ∈ sourceIsospectralSet hp φ) :
    sourceIsospectralSet hp ψ = sourceIsospectralSet hp φ := by
  ext χ
  constructor
  · intro hχ
    exact ⟨hχ.1.trans hψ.1, fun z => (hχ.2 z).trans (hψ.2 z)⟩
  · intro hχ
    exact ⟨hχ.1.trans hψ.1.symm, fun z => (hχ.2 z).trans (hψ.2 z).symm⟩

/-- Distinct original isospectral sets are disjoint. -/
theorem sourceIsospectralSet_eq_or_disjoint (hp : p ≠ ⊤)
    (φ ψ : realTypeSourceSubmodule p) :
    sourceIsospectralSet hp φ = sourceIsospectralSet hp ψ ∨
      Disjoint (sourceIsospectralSet hp φ) (sourceIsospectralSet hp ψ) := by
  by_cases h : ∃ χ, χ ∈ sourceIsospectralSet hp φ ∧ χ ∈ sourceIsospectralSet hp ψ
  · obtain ⟨χ,hφ,hψ⟩ := h
    exact Or.inl ((sourceIsospectralSet_eq_of_mem hp hφ).symm.trans
      (sourceIsospectralSet_eq_of_mem hp hψ))
  · right
    exact Set.disjoint_left.mpr (fun χ hφ hψ => h ⟨χ,hφ,hψ⟩)

/-- The original periodic spectral classes cover the entire real phase space. -/
theorem iUnion_sourceIsospectralSet (hp : p ≠ ⊤) :
    (⋃ φ : realTypeSourceSubmodule p, sourceIsospectralSet hp φ) = univ := by
  ext ψ
  simp only [mem_iUnion,mem_univ,iff_true]
  exact ⟨ψ,mem_sourceIsospectralSet_self hp ψ⟩

/-- A physical ordinary solution remains in exactly its initial spectral class. -/
theorem sourceIsospectralSet_of_isOrdinaryNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsOrdinaryNLSSolutionOn univ φ γ) (τ : ℝ) :
    sourceIsospectralSet hp (γ τ) = sourceIsospectralSet hp φ :=
  sourceIsospectralSet_eq_of_mem hp
    (isospectral_of_isOrdinaryNLSSolutionOn_univ hp hp1 hp2 hγ τ)

/-- Membership in any fixed spectral class is invariant along the physical solution. -/
theorem mem_sourceIsospectralSet_of_isOrdinaryNLSSolutionOn_univ_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsOrdinaryNLSSolutionOn univ φ γ) (τ : ℝ)
    (ψ : realTypeSourceSubmodule p) :
    γ τ ∈ sourceIsospectralSet hp ψ ↔ φ ∈ sourceIsospectralSet hp ψ := by
  have ht := isospectral_of_isOrdinaryNLSSolutionOn_univ hp hp1 hp2 hγ τ
  constructor
  · intro h
    exact ⟨ht.1.symm.trans h.1, fun z => (ht.2 z).symm.trans (h.2 z)⟩
  · intro h
    exact ⟨ht.1.trans h.1, fun z => (ht.2 z).trans (h.2 z)⟩

end NLS.ZakharovShabat
