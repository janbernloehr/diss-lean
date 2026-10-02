import NLS.Poisson.RegularSourceCotangentIntegral

/-! # Linear combinations of regular cotangents

Adding the actual source cotangents and their Hilbert coefficient
witnesses preserves regularity. The physical Fourier pairing obeys
the corresponding bilinear rules at every source exponent.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson.RegularSourceCotangent
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def add (L M : RegularSourceCotangent p) : RegularSourceCotangent p where
  toCotangent := L.toCotangent + M.toCotangent
  coefficients := L.coefficients + M.coefficients
  fst_eq := by intro n; change L.coefficients.1 n + M.coefficients.1 n = _; rw [L.fst_eq,M.fst_eq]; rfl
  snd_eq := by intro n; change L.coefficients.2 n + M.coefficients.2 n = _; rw [L.snd_eq,M.snd_eq]; rfl

@[simp] theorem bivector_add_left (L M N : RegularSourceCotangent p) :
    (L.add M).bivector N = L.bivector N + M.bivector N := by
  change hilbertPairBivector (L.coefficients + M.coefficients) N.coefficients = _
  simp only [map_add,add_apply,bivector]

@[simp] theorem bivector_add_right (L M N : RegularSourceCotangent p) :
    L.bivector (M.add N) = L.bivector M + L.bivector N := by
  change hilbertPairBivector L.coefficients (M.coefficients + N.coefficients) = _
  simp only [map_add,bivector]

/-- The determinant rule for two linear combinations of a canonical
pair, allowing distinct indices through the scalar `k`. -/
theorem bivector_linear_combination_of_canonical
    (L T M S : RegularSourceCotangent p) (k a b c d : ℂ)
    (hLM : L.bivector M = 0) (hTS : T.bivector S = 0)
    (hTM : T.bivector M = k) (hLS : L.bivector S = -k) :
    ((L.smul a).add (T.smul b)).bivector ((M.smul c).add (S.smul d)) = (b*c-a*d)*k := by
  simp only [bivector_add_left,bivector_add_right,bivector_smul_left,bivector_smul_right,
    hLM,hTS,hTM,hLS]
  ring

end NLS.Poisson.RegularSourceCotangent
