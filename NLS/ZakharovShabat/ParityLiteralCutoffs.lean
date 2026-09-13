import NLS.ZakharovShabat.ParityCentralCutoffGrowth
import NLS.ZakharovShabat.ParitySpectralCutoffs

/-!
# Intrinsic formulas for the literal parity cutoffs

Even cutoffs are normalized central parity polynomials at radius index `2M`.
The literal odd cutoff contains the same central odd indices and one extra
positive boundary pair at `2M+1`. These identities are exact at spectral zeros.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- The literal even indices are exactly the even part of the doubled central interval. -/
theorem prod_even_centralParityIndices (f : ℤ → ℂ) (M : ℕ) :
    (∏ n ∈ Finset.Icc (-(M : ℤ)) M, f (2*n)) = ∏ n ∈ centralParityIndices (2*M) 0, f n := by
  apply Finset.prod_bij (fun n _ => 2*n)
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [centralParityIndices, Finset.mem_filter, Finset.mem_Icc, Nat.cast_mul, Nat.cast_ofNat]
    omega
  · intro a _ b _ hab
    omega
  · intro b hb
    simp only [centralParityIndices, Finset.mem_filter, Finset.mem_Icc, Nat.cast_mul, Nat.cast_ofNat] at hb
    refine ⟨b/2, ?_, by omega⟩
    simp only [Finset.mem_Icc]
    omega
  · intro n _
    rfl

/-- The literal odd cutoff is the doubled central odd product times its extra positive boundary factor. -/
theorem prod_odd_centralParityIndices (f : ℤ → ℂ) (M : ℕ) :
    (∏ n ∈ Finset.Icc (-(M : ℤ)) M, f (2*n+1)) =
      (∏ n ∈ centralParityIndices (2*M) 1, f n) * f (2*(M : ℤ)+1) := by
  have he : (∏ n ∈ Finset.Icc (-(M : ℤ)) M, f (2*n+1)) =
      ∏ n ∈ insert (2*(M : ℤ)+1) (centralParityIndices (2*M) 1), f n := by
    apply Finset.prod_bij (fun n _ => 2*n+1)
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_insert, centralParityIndices, Finset.mem_filter, Finset.mem_Icc,
        Nat.cast_mul, Nat.cast_ofNat]
      omega
    · intro a _ b _ hab
      omega
    · intro b hb
      simp only [Finset.mem_insert, centralParityIndices, Finset.mem_filter, Finset.mem_Icc,
        Nat.cast_mul, Nat.cast_ofNat] at hb
      refine ⟨(b-1)/2, ?_, by omega⟩
      simp only [Finset.mem_Icc]
      omega
    · intro n _
      rfl
  have hn : 2*(M : ℤ)+1 ∉ centralParityIndices (2*M) 1 := by
    simp only [centralParityIndices, Finset.mem_filter, Finset.mem_Icc, Nat.cast_mul, Nat.cast_ofNat]
    omega
  rw [he, Finset.prod_insert hn, mul_comm]

/-- The constant normalization of the finite central parity factors. -/
def centralParityNormalization (N : ℕ) (r : ℤ) : ℂ :=
  ∏ n ∈ centralParityIndices N r, spectralPairDenominator n

/-- Every parity normalization is nonzero, including the exceptional zero-mode denominator. -/
theorem centralParityNormalization_ne_zero (N : ℕ) (r : ℤ) : centralParityNormalization N r ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun n _ => spectralPairDenominator_ne_zero n)

open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A normalized finite product of completed central pairs is intrinsic at every larger cutoff. -/
theorem CompletePeriodicParityPairs.central_factor_prod_eq {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (K : ℕ) (hNK : N ≤ K)
    (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    (∏ n ∈ centralParityIndices K r, spectralPairFactor ξ η z n) =
      centralParityPolynomial hp (weightedBaseToPair w φ) K r z / centralParityNormalization K r := by
  simp only [spectralPairFactor_eq_div, Finset.prod_div_distrib, h.central_prod_eq K hNK r hr z,
    centralParityNormalization]

/-- The even cutoff is exactly the intrinsically normalized central even polynomial. -/
theorem CompletePeriodicParityPairs.evenCutoff_eq_central {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (M : ℕ) (hM : N ≤ 2*M) (z : ℂ) :
    evenSpectralPairCutoff ξ η z M =
      -centralParityPolynomial hp (weightedBaseToPair w φ) (2*M) 0 z / centralParityNormalization (2*M) 0 := by
  rw [evenSpectralPairCutoff, prod_even_centralParityIndices, h.central_factor_prod_eq _ hM 0 (Or.inl rfl) z]
  ring

/-- The odd cutoff is the intrinsic central odd polynomial times the retained boundary pair. -/
theorem CompletePeriodicParityPairs.oddCutoff_eq_central {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (M : ℕ) (hM : N ≤ 2*M) (z : ℂ) :
    oddSpectralPairCutoff ξ η z M =
      (4*centralParityPolynomial hp (weightedBaseToPair w φ) (2*M) 1 z / centralParityNormalization (2*M) 1) *
        spectralPairFactor ξ η z (2*(M : ℤ)+1) := by
  rw [oddSpectralPairCutoff, prod_odd_centralParityIndices, h.central_factor_prod_eq _ hM 1 (Or.inr rfl) z]
  ring

end NLS.ZakharovShabat
