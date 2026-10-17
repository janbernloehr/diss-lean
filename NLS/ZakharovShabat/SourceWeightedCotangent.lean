import NLS.Poisson.WeightedRegularSourceCotangent
import NLS.ZakharovShabat.SourceWeightedInclusion

/-! # Restriction of actual regular cotangents to weighted sources

The original coefficient-preserving inclusion preserves the verified Fourier
coefficients of a regular cotangent and hence its physical Poisson pairings.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace RegularSourceCotangent
open ZakharovShabat

/-- Pull back along the actual inclusion; all raw Fourier coefficient witnesses stay the same. -/
def restrictWeight (w : SpectralWeight) (L : RegularSourceCotangent p) :
    WeightedRegularSourceCotangent (sourceFrequencyWeight w) p where
  toCotangent := L.toCotangent.comp (originalWeightedSourceCLM w)
  coefficients := L.coefficients
  fst_eq := by intro n; simpa using L.fst_eq n
  snd_eq := by intro n; simpa using L.snd_eq n

@[simp] theorem bivector_restrictWeight (w : SpectralWeight) (L M : RegularSourceCotangent p) :
    (L.restrictWeight w).bivector (M.restrictWeight w) = L.bivector M := rfl

end RegularSourceCotangent
end NLS.Poisson
