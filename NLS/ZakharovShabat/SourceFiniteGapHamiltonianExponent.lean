import NLS.ZakharovShabat.SourceFiniteGapRenormalizedHamiltonian
import NLS.ZakharovShabat.SourceActionExponentDifferential

/-! # Exponent compatibility of physical finite-gap Hamiltonians

Identical Fourier coefficients give identical smooth physical representatives.
Consequently the physical hierarchy and its renormalized correction are
unchanged when the same source is included in a larger exponent space.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The smooth physical representative depends only on the actual coefficients. -/
theorem sourceFiniteGapPhysicalPair_eq_of_coefficients
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q)
    (φ : realTypeSourceSubmodule p) (ψ : realTypeSourceSubmodule q)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (hg : ψ ∈ sourceFiniteGapLocus hq hq1)
    (he : ∀ n, φ.val.fst n = ψ.val.fst n ∧ φ.val.snd n = ψ.val.snd n) :
    sourceFiniteGapPhysicalPair hp hp1 φ hf = sourceFiniteGapPhysicalPair hq hq1 ψ hg := by
  apply Prod.ext
  · change periodOneSynthesis _ = periodOneSynthesis _
    congr 1
    ext n
    exact (he n).1
  · change periodOneSynthesis _ = periodOneSynthesis _
    congr 1
    ext n
    exact (he n).2

/-- All physical hierarchy Hamiltonians agree across coefficient-identical sources. -/
theorem sourceFiniteGapNLSHamiltonian_eq_of_coefficients
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q)
    (φ : realTypeSourceSubmodule p) (ψ : realTypeSourceSubmodule q)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (hg : ψ ∈ sourceFiniteGapLocus hq hq1)
    (he : ∀ n, φ.val.fst n = ψ.val.fst n ∧ φ.val.snd n = ψ.val.snd n) (j : ℕ) :
    sourceFiniteGapNLSHamiltonian hp hp1 φ hf j = sourceFiniteGapNLSHamiltonian hq hq1 ψ hg j := by
  simp only [sourceFiniteGapNLSHamiltonian,
    sourceFiniteGapPhysicalPair_eq_of_coefficients hp hq hp1 hq1 φ ψ hf hg he]

/-- The physical renormalization is preserved under source exponent inclusion. -/
theorem sourceFiniteGapRenormalizedHamiltonian_real_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapRenormalizedHamiltonian hp hp1 φ hf =
      sourceFiniteGapRenormalizedHamiltonian hq hq1 (realTypeSourceExponentInclusion hpq φ)
        ((sourceFiniteGapLocus_exponent_iff hp hq hp1 hq1 hpq φ).mp hf) := by
  have hg := (sourceFiniteGapLocus_exponent_iff hp hq hp1 hq1 hpq φ).mp hf
  unfold sourceFiniteGapRenormalizedHamiltonian
  rw [sourceFiniteGapNLSHamiltonian_eq_of_coefficients hp hq hp1 hq1 φ
    (realTypeSourceExponentInclusion hpq φ) hf hg (fun _ => ⟨rfl,rfl⟩) 3,
    sourceFiniteGapNLSHamiltonian_eq_of_coefficients hp hq hp1 hq1 φ
      (realTypeSourceExponentInclusion hpq φ) hf hg (fun _ => ⟨rfl,rfl⟩) 1]
  congr 1
  exact tsum_congr (fun n => congrArg (fun a : ℂ => (2*(n:ℂ)*Real.pi)^2*a)
    (sourceComplexAction_real_exponent hp hq hp1 hq1 hpq n φ))

end NLS.ZakharovShabat
