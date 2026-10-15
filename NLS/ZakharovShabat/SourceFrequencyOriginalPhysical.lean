import NLS.ZakharovShabat.SourceFrequencyOriginalHilbert
import NLS.ZakharovShabat.SourceSecondMomentFrequencyTheorem20_4

/-!
# Physical meaning and exponent compatibility of the original frequency

The action-space maps recover the independently constructed physical
finite-gap frequency after subtracting four times the physical mass and
the free dispersion. Their values agree for equal Fourier coefficients.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {U : Set (Coeff q)} {F : Coeff q → Coeff q}

/-- Exact physical normalization of the original higher-exponent action frequency. -/
theorem SourceOriginalFrequencyData.physical_finiteGap
    (E : SourceOriginalFrequencyData D U F)
    {W₂ B₂ V₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D₂ : SourceSection17OriginalData (by simp) (by norm_num) W₂ B₂ V₂ s₂)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    F (sourceActionSequence hp hp1 s φ.val) n =
      D₂.complex.finiteGapFrequencyAtExponent hp hp1 φ hf n -
        4*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1 - (2*(n:ℂ)*Real.pi)^2 := by
  obtain ⟨Wa,sa,A,P,hs,hrec⟩ := E.spectral
  exact (hrec φ n).trans (A.renormalizedFrequency_eq_physical_finiteGap_all_exponents D₂.complex hs φ hf n)

/-- The fixed Hilbert frequency has the same physical normalization. -/
theorem SourceOriginalHilbertFrequencyData.physical_finiteGap
    {W₂ B₂ V₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D₂ : SourceSection17OriginalData (by simp) (by norm_num) W₂ B₂ V₂ s₂}
    {U₂ : Set (Coeff 1)} {ωstar : Coeff 1 → ℤ → ℂ}
    (H : SourceOriginalHilbertFrequencyData D₂ U₂ ωstar)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    ωstar (sourceActionSequence (q := 1) (by simp) (by norm_num) s₂ φ.val) n =
      D₂.complex.finiteGapFrequencyAtExponent (by simp) (by norm_num) φ hf n -
        4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 - (2*(n:ℂ)*Real.pi)^2 := by
  obtain ⟨Wa,sa,A,P,hs,hrec⟩ := H.spectral
  exact (hrec φ n).trans (A.renormalizedFrequency_eq_physical_finiteGap_all_exponents D₂.complex hs φ hf n)

/-- Independently constructed original action maps agree on every real
potential represented by the same Fourier coefficients at two exponents. -/
theorem SourceOriginalFrequencyData.eq_of_coefficients
    {p' q' : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ q')] [p'.HolderTriple p' q']
    {hp' : p' ≠ ⊤} {hp1' : 1 < p'} {W₀' W' V' : Set (CoeffPair p')}
    {s' : (n : ℤ) → CoeffPair p' → DeletedCoeff p' n}
    {D' : SourceSection17OriginalData hp' hp1' W₀' W' V' s'}
    {U' : Set (Coeff q')} {F' : Coeff q' → Coeff q'}
    (E : SourceOriginalFrequencyData D U F) (E' : SourceOriginalFrequencyData D' U' F')
    (φ : realTypeSourceSubmodule p) (ψ : realTypeSourceSubmodule p')
    (hcoeff : ∀ j : ℤ, ψ.val.fst j = φ.val.fst j ∧ ψ.val.snd j = φ.val.snd j) (n : ℤ) :
    F (sourceActionSequence hp hp1 s φ.val) n = F' (sourceActionSequence hp' hp1' s' ψ.val) n := by
  obtain ⟨Wa,sa,A,P,hs,hrec⟩ := E.spectral
  obtain ⟨Wa',sa',A',P',hs',hrec'⟩ := E'.spectral
  exact (hrec φ n).trans ((A.renormalizedFrequency_real_eq_of_coefficients A' hs hs' φ ψ hcoeff n).trans
    (hrec' ψ n).symm)

end NLS.ZakharovShabat
