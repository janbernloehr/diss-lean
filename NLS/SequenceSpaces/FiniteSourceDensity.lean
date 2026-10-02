import NLS.SequenceSpaces.FiniteSourceCoefficients

/-! # Density of finite Fourier source pairs -/

noncomputable section
open scoped ENNReal
namespace NLS.CoeffPair
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem denseRange_ofFinsupp (hp : p ≠ ⊤) : DenseRange (ofFinsupp (p := p)) :=
  (toMax p).symm.surjective.denseRange.comp
    ((Coeff.denseRange_ofFinsupp hp).prodMap (Coeff.denseRange_ofFinsupp hp)) (toMax p).symm.continuous

/-- Continuous identities on finite Fourier inputs determine the entire
source map at every finite exponent. No real-type restriction is needed. -/
theorem eq_of_continuous_of_finsupp {E : Type*} [TopologicalSpace E] [T2Space E]
    (hp : p ≠ ⊤) (f g : CoeffPair p → E) (hf : Continuous f) (hg : Continuous g)
    (hfinite : ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ), f (ofFinsupp a) = g (ofFinsupp a)) : f = g :=
  (denseRange_ofFinsupp hp).equalizer hf hg (funext hfinite)

end NLS.CoeffPair
