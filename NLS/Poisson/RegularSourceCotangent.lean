import NLS.Poisson.SourceBivector

/-!
# Source cotangents with square-summable Fourier coefficients

Below exponent two, a continuous source cotangent need not have Hilbert
coefficients. This structure records and verifies that extra regularity.
Its physical Poisson pairing is absolutely convergent, independent of
the coefficient witness, and preserved by every exponent restriction.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A genuine continuous source cotangent with square-summable values
on the two families of unit Fourier directions. -/
structure RegularSourceCotangent (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  toCotangent : CoeffPair p →L[ℂ] ℂ
  coefficients : Coeff 2 × Coeff 2
  fst_eq : ∀ n : ℤ, coefficients.1 n = toCotangent (CoeffPair.inlCLM (lp.single p n 1))
  snd_eq : ∀ n : ℤ, coefficients.2 n = toCotangent (CoeffPair.inrCLM (lp.single p n 1))

namespace RegularSourceCotangent

/-- A coefficient witness is determined by the underlying cotangent. -/
theorem coefficients_eq_of_toCotangent_eq (L M : RegularSourceCotangent p)
    (h : L.toCotangent = M.toCotangent) : L.coefficients = M.coefficients := by
  apply Prod.ext <;> ext n
  · rw [L.fst_eq, M.fst_eq, h]
  · rw [L.snd_eq, M.snd_eq, h]

/-- At exponents at least two, every continuous cotangent is regular. -/
def ofCotangent (h2p : (2 : ℝ≥0∞) ≤ p) (L : CoeffPair p →L[ℂ] ℂ) :
    RegularSourceCotangent p where
  toCotangent := L
  coefficients := CoeffPair.cotangentCoefficients h2p L
  fst_eq := CoeffPair.cotangentCoefficients_fst h2p L
  snd_eq := CoeffPair.cotangentCoefficients_snd h2p L

/-- Restriction preserves the actual coefficients, including when the
smaller exponent is below two. -/
def restrict (hpq : p ≤ q) (L : RegularSourceCotangent q) : RegularSourceCotangent p where
  toCotangent := L.toCotangent.comp (CoeffPair.exponentInclusion hpq)
  coefficients := L.coefficients
  fst_eq := by intro n; rw [L.fst_eq]; congr 1
  snd_eq := by intro n; rw [L.snd_eq]; congr 1

/-- The physical Poisson pairing, with frequency reversal and sign `-i`. -/
def bivector (L M : RegularSourceCotangent p) : ℂ :=
  hilbertPairBivector L.coefficients M.coefficients

theorem bivector_antisymm (L M : RegularSourceCotangent p) :
    L.bivector M = -M.bivector L := hilbertPairBivector_antisymm _ _

@[simp] theorem bivector_self (L : RegularSourceCotangent p) : L.bivector L = 0 :=
  hilbertPairBivector_self _

theorem bivector_congr {L L' M M' : RegularSourceCotangent p}
    (hL : L.toCotangent = L'.toCotangent) (hM : M.toCotangent = M'.toCotangent) :
    L.bivector M = L'.bivector M' := by
  unfold bivector
  rw [coefficients_eq_of_toCotangent_eq L L' hL, coefficients_eq_of_toCotangent_eq M M' hM]

@[simp] theorem bivector_restrict (hpq : p ≤ q) (L M : RegularSourceCotangent q) :
    (L.restrict hpq).bivector (M.restrict hpq) = L.bivector M := rfl

/-- This extends the existing source bivector exactly on its old domain. -/
@[simp] theorem bivector_ofCotangent (h2p : (2 : ℝ≥0∞) ≤ p)
    (L M : CoeffPair p →L[ℂ] ℂ) :
    (ofCotangent h2p L).bivector (ofCotangent h2p M) = sourceBivector h2p L M := rfl

theorem norm_bivector_le (L M : RegularSourceCotangent p) :
    ‖L.bivector M‖ ≤ 2 * ‖L.coefficients‖ * ‖M.coefficients‖ :=
  norm_hilbertPairBivector_le _ _

theorem summable_norm (L M : RegularSourceCotangent p) :
    Summable (fun n : ℤ => ‖
      L.toCotangent (CoeffPair.inlCLM (lp.single p n 1)) *
        M.toCotangent (CoeffPair.inrCLM (lp.single p (-n) 1)) -
      L.toCotangent (CoeffPair.inrCLM (lp.single p n 1)) *
        M.toCotangent (CoeffPair.inlCLM (lp.single p (-n) 1))‖) := by
  have h := ((summable_norm_reflectedHilbertPairing L.coefficients.1 M.coefficients.2).of_norm.sub
    (summable_norm_reflectedHilbertPairing L.coefficients.2 M.coefficients.1).of_norm).norm
  simpa only [L.fst_eq, L.snd_eq, M.fst_eq, M.snd_eq] using h

/-- The bracket is the absolutely convergent literal Fourier formula
of the original source cotangents, not an arbitrarily chosen extension. -/
theorem bivector_eq_tsum (L M : RegularSourceCotangent p) :
    L.bivector M = -I * ∑' n : ℤ,
      (L.toCotangent (CoeffPair.inlCLM (lp.single p n 1)) *
        M.toCotangent (CoeffPair.inrCLM (lp.single p (-n) 1)) -
      L.toCotangent (CoeffPair.inrCLM (lp.single p n 1)) *
        M.toCotangent (CoeffPair.inlCLM (lp.single p (-n) 1))) := by
  rw [bivector, hilbertPairBivector_apply, reflectedHilbertPairing_apply,
    reflectedHilbertPairing_apply,
    ← (summable_norm_reflectedHilbertPairing L.coefficients.1 M.coefficients.2).of_norm.tsum_sub
      (summable_norm_reflectedHilbertPairing L.coefficients.2 M.coefficients.1).of_norm]
  simp only [L.fst_eq, L.snd_eq, M.fst_eq, M.snd_eq]

end RegularSourceCotangent
end NLS.Poisson
