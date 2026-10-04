import NLS.ZakharovShabat.SourceFiniteGapLemma20_2
import NLS.ZakharovShabat.SourceFiniteGapMassExponent

/-! # Physical finite-gap frequencies at every source exponent

Every actual finite-gap source has a unique Hilbert representative with
the same Fourier coefficients. Its frequency is the already constructed
physical Hamiltonian derivative, and is independent of the chosen
Hilbert representative and Birkhoff realization. No moment sum enters
this definition.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The coefficient-preserving physical Hilbert representative. -/
def sourceFiniteGapHilbertModel (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    realTypeSourceSubmodule 2 := (sourceFiniteGap_exists_hilbert_mass_model hp hp1 φ hf).choose

theorem sourceFiniteGapHilbertModel_coefficients (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (j : ℤ) :
    (sourceFiniteGapHilbertModel hp hp1 φ hf).val.fst j = φ.val.fst j ∧
      (sourceFiniteGapHilbertModel hp hp1 φ hf).val.snd j = φ.val.snd j :=
  (sourceFiniteGap_exists_hilbert_mass_model hp hp1 φ hf).choose_spec.1 j

theorem sourceFiniteGapHilbertModel_mem (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapHilbertModel hp hp1 φ hf ∈ sourceFiniteGapLocus (by simp) (by norm_num) :=
  (sourceFiniteGap_exists_hilbert_mass_model hp hp1 φ hf).choose_spec.2.1

/-- The representative is uniquely determined by the original coefficients. -/
theorem sourceFiniteGapHilbertModel_eq_of_coefficients (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (ψ : realTypeSourceSubmodule 2)
    (hcoeff : ∀ j : ℤ, ψ.val.fst j = φ.val.fst j ∧ ψ.val.snd j = φ.val.snd j) :
    sourceFiniteGapHilbertModel hp hp1 φ hf = ψ := by
  apply Subtype.ext
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext j
    exact (sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf j).1.trans (hcoeff j).1.symm
  · ext j
    exact (sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf j).2.trans (hcoeff j).2.symm

/-- The representative gives exactly the same smooth physical
potential, pointwise, not merely the same spectral invariants. -/
theorem sourceFiniteGapHilbertModel_physicalPair (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapPhysicalPair (by simp) (by norm_num) (sourceFiniteGapHilbertModel hp hp1 φ hf)
      (sourceFiniteGapHilbertModel_mem hp hp1 φ hf) = sourceFiniteGapPhysicalPair hp hp1 φ hf := by
  apply Prod.ext
  · apply congrArg NLS.Fourier.periodOneSynthesis
    apply Subtype.ext
    funext j
    exact (sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf j).1
  · apply congrArg NLS.Fourier.periodOneSynthesis
    apply Subtype.ext
    funext j
    exact (sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf j).2

/-- Every physical Hamiltonian is preserved by the Hilbert realization. -/
theorem sourceFiniteGapHilbertModel_hamiltonian (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (k : ℕ) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (sourceFiniteGapHilbertModel hp hp1 φ hf)
      (sourceFiniteGapHilbertModel_mem hp hp1 φ hf) k = sourceFiniteGapNLSHamiltonian hp hp1 φ hf k := by
  simp only [sourceFiniteGapNLSHamiltonian,sourceFiniteGapHilbertModel_physicalPair]

/-- The mass subtracted from the frequency is the original source's
physical first Hamiltonian, not a new model-dependent quantity. -/
theorem sourceFiniteGapHilbertModel_hamiltonian_one (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (sourceFiniteGapHilbertModel hp hp1 φ hf)
      (sourceFiniteGapHilbertModel_mem hp hp1 φ hf) 1 = sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1 :=
  sourceFiniteGapHilbertModel_hamiltonian hp hp1 φ hf 1

namespace SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The physical finite-gap frequency at any finite source exponent,
computed through the unique representative of the same potential. -/
def finiteGapFrequencyAtExponent
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) : ℂ :=
  D.finiteGapFrequency (sourceFiniteGapHilbertModel hp hp1 φ hf)
    (sourceFiniteGapHilbertModel_mem hp hp1 φ hf) n

/-- At exponent two, this is exactly the previously defined physical frequency. -/
theorem finiteGapFrequencyAtExponent_two
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    D.finiteGapFrequencyAtExponent (by simp) (by norm_num) φ hf n = D.finiteGapFrequency φ hf n := by
  unfold finiteGapFrequencyAtExponent
  simp only [sourceFiniteGapHilbertModel_eq_of_coefficients (by simp) (by norm_num) φ hf φ
    (fun _ => ⟨rfl,rfl⟩)]

/-- The transported physical frequency is independent of Birkhoff coordinates. -/
theorem finiteGapFrequencyAtExponent_independent_coordinates
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V u)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    D.finiteGapFrequencyAtExponent hp hp1 φ hf n = E.finiteGapFrequencyAtExponent hp hp1 φ hf n :=
  D.finiteGapFrequency_independent_coordinates E _ _ n

/-- Equal Fourier coefficients at different source exponents give the
same physical frequency, through the unique common Hilbert representative. -/
theorem finiteGapFrequencyAtExponent_eq_of_coefficients
    {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q)
    (φ : realTypeSourceSubmodule p) (ψ : realTypeSourceSubmodule q)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (hg : ψ ∈ sourceFiniteGapLocus hq hq1)
    (hcoeff : ∀ j : ℤ, ψ.val.fst j = φ.val.fst j ∧ ψ.val.snd j = φ.val.snd j) (n : ℤ) :
    D.finiteGapFrequencyAtExponent hp hp1 φ hf n = D.finiteGapFrequencyAtExponent hq hq1 ψ hg n := by
  have he := sourceFiniteGapHilbertModel_eq_of_coefficients hp hp1 φ hf
    (sourceFiniteGapHilbertModel hq hq1 ψ hg) (fun j =>
      ⟨(sourceFiniteGapHilbertModel_coefficients hq hq1 ψ hg j).1.trans (hcoeff j).1,
        (sourceFiniteGapHilbertModel_coefficients hq hq1 ψ hg j).2.trans (hcoeff j).2⟩)
  unfold finiteGapFrequencyAtExponent
  simp only [he]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
