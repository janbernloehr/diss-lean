import NLS.ZakharovShabat.PeriodicSpectralProducts

/-!
# Cancellation of the central free factors

After the cutoff contains the central cluster, the product is a literal finite
product of actual spectral factors with constant denominators. The apparent
spectral-parameter denominators in the relative construction cancel exactly.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- The source's squared normalization, with denominator one at the zero mode. -/
def spectralPairDenominator (n : ℤ) : ℂ :=
  if n = 0 then 1 else ((Real.pi : ℂ)*n)^2

theorem spectralPairDenominator_ne_zero (n : ℤ) : spectralPairDenominator n ≠ 0 := by
  unfold spectralPairDenominator
  split_ifs with hn
  · exact one_ne_zero
  · exact pow_ne_zero _ (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (Int.cast_ne_zero.mpr hn))

theorem spectralPairFactor_eq_div (ξ η : ℤ → ℂ) (z : ℂ) (n : ℤ) :
    spectralPairFactor ξ η z n = (ξ n-z)*(η n-z)/spectralPairDenominator n := by
  unfold spectralPairFactor spectralPairDenominator
  split_ifs <;> simp only [div_one]

/-- Constant normalization for the finite central cluster. -/
def centralSpectralNormalization (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralPairDenominator n

theorem centralSpectralNormalization_ne_zero (N : ℕ) : centralSpectralNormalization N ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun n _ => spectralPairDenominator_ne_zero n)

/-- The artificial central factors contribute exactly the free polynomial divided by constants. -/
theorem prod_centralFreeCompletion (N : ℕ) (ξ η : ℤ → ℂ) (z : ℂ) :
    (∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      spectralPairFactor (centralFreeCompletion N ξ) (centralFreeCompletion N η) z n) =
        centralFreePolynomial N z / centralSpectralNormalization N := by
  rw [centralFreePolynomial, centralSpectralNormalization, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro n hn
  have hn' : ¬ N < n.natAbs := by
    simp only [Finset.mem_Icc] at hn
    omega
  simp only [spectralPairFactor_eq_div, centralFreeCompletion, if_neg hn', pow_two]

open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every sufficiently large cutoff uses exactly the actual central polynomial and high pairs.
All remaining denominators are nonzero constants independent of the spectral parameter. -/
theorem periodicSpectralProductCutoff_eq (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (z : {z : ℂ // z ∉ freeLattice}) (M : ℕ) (hM : N ≤ M) :
    periodicSpectralProductCutoff hp φ N ξ η z M =
      (-4 * centralPeriodicPolynomial hp φ N z.val / centralSpectralNormalization N) *
        ∏ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ),
          spectralPairFactor ξ η z.val n := by
  have hsub : Finset.Icc (-(N : ℤ)) (N : ℤ) ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    constructor <;> omega
  have htail : (∏ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ),
      spectralPairFactor (centralFreeCompletion N ξ) (centralFreeCompletion N η) z.val n) =
      ∏ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ),
        spectralPairFactor ξ η z.val n := by
    apply Finset.prod_congr rfl
    intro n hn
    have hn' : N < n.natAbs := by
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
      omega
    simp only [spectralPairFactor, centralFreeCompletion, if_pos hn']
  unfold periodicSpectralProductCutoff spectralPairPartialProduct
  rw [← Finset.prod_sdiff hsub, htail, prod_centralFreeCompletion]
  have hd := centralFreePolynomial_ne_zero N z.val z.property
  have hc := centralSpectralNormalization_ne_zero N
  field_simp

end NLS.ZakharovShabat
