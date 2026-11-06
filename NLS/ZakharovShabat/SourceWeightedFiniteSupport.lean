import NLS.ZakharovShabat.SourceWeightedRealMembership
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.SequenceSpaces.Truncation

/-! # Original weighted representatives of finite Fourier sources

Finite Fourier support supplies every weighted exponent representative
coefficient-for-coefficient. This makes no spectral finite-gap assertion.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A real finite Fourier source has the same original coefficients in
every weighted real source space, at any Banach exponent. -/
theorem exists_weightedRealSource_of_finiteSupport
    (w : SpectralWeight) (φ : realTypeSourceSubmodule p)
    (hfst : Coeff.HasFiniteSupport φ.val.fst) (hsnd : Coeff.HasFiniteSupport φ.val.snd) :
    ∃ a : weightedRealSourceSubmodule (p := q) w, ∀ n : ℤ,
      (originalWeightedRealSource w a).val.fst n = φ.val.fst n ∧
      (originalWeightedRealSource w a).val.snd n = φ.val.snd n := by
  classical
  obtain ⟨S,hS⟩ := hfst
  obtain ⟨T,hT⟩ := hsnd
  let f : ℤ →₀ ℂ := Finsupp.onFinset S (fun n => φ.val.fst n) (by
    intro n hn
    by_contra h
    exact hn (hS n h))
  let g : ℤ →₀ ℂ := Finsupp.onFinset T (fun n => φ.val.snd n) (by
    intro n hn
    by_contra h
    exact hn (hT n h))
  let b : WeightedCoeffPair (sourceFrequencyWeight w) q := WithLp.toLp q
    (WeightedCoeff.ofFinsupp (sourceFrequencyWeight w) q f,
      WeightedCoeff.ofFinsupp (sourceFrequencyWeight w) q g)
  have hb : b ∈ weightedRealSourceSubmodule w := by
    rw [mem_weightedRealSourceSubmodule_iff]
    exact φ.property
  refine ⟨⟨b,hb⟩,?_⟩
  intro n
  constructor
  · exact originalWeightedRealSource_fst w ⟨b,hb⟩ n
  · exact originalWeightedRealSource_snd w ⟨b,hb⟩ n

end NLS.ZakharovShabat
