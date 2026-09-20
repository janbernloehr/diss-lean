import NLS.ZakharovShabat.PerturbedSpectralProducts

/-!
# Normalized single spectral products

The symmetric cutoffs in Lemma 8.5 have prefactor two and denominator one
at index zero. Their free value tends to minus twice the sine.
-/

noncomputable section
open Filter Topology
namespace NLS.ZakharovShabat

/-- The exceptional zero-mode denominator in the single product. -/
def singleSpectralDenominator (n : ℤ) : ℂ :=
  if n = 0 then 1 else (Real.pi : ℂ)*n

@[simp] theorem singleSpectralDenominator_ne_zero (n : ℤ) :
    singleSpectralDenominator n ≠ 0 := by
  by_cases hn : n = 0
  · simp [singleSpectralDenominator, hn]
  · exact (if_neg hn).trans_ne (mul_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (Int.cast_ne_zero.mpr hn))

/-- One root contributes one linear factor, including at index zero. -/
def singleSpectralFactor (ξ : ℤ → ℂ) (z : ℂ) (n : ℤ) : ℂ :=
  (ξ n-z)/singleSpectralDenominator n

/-- Literal symmetric cutoffs of the normalized derivative product. -/
def singleSpectralPartialProduct (ξ : ℤ → ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  2 * ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), singleSpectralFactor ξ z n

/-- Pairing positive and negative free modes gives the unsquared Euler factors. -/
theorem singleSpectralPartialProduct_free_eq (z : ℂ) (N : ℕ) :
    singleSpectralPartialProduct (fun n => (Real.pi : ℂ)*n) z N =
      -2*z * ∏ j ∈ Finset.range N, (1-z^2/((Real.pi : ℂ)*((j : ℂ)+1))^2) := by
  rw [singleSpectralPartialProduct, prod_symmetric_interval]
  have hp : ∀ j : ℕ,
      singleSpectralFactor (fun n => (Real.pi : ℂ)*n) z ((j : ℤ)+1) *
      singleSpectralFactor (fun n => (Real.pi : ℂ)*n) z (-((j : ℤ)+1)) =
      1-z^2/((Real.pi : ℂ)*((j : ℂ)+1))^2 := by
    intro j
    simp only [singleSpectralFactor, singleSpectralDenominator, if_neg (by omega : (j : ℤ)+1 ≠ 0),
      if_neg (by omega : -((j : ℤ)+1) ≠ 0)]
    push_cast
    have hj : (j : ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero j
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  simp only [hp]
  simp only [singleSpectralFactor, singleSpectralDenominator, Int.cast_zero,
    mul_zero, zero_sub, ↓reduceIte, div_one]
  ring

/-- The sign and prefactor agree with the derivative of the free discriminant. -/
theorem tendsto_singleSpectralPartialProduct_free (z : ℂ) :
    Tendsto (singleSpectralPartialProduct (fun n => (Real.pi : ℂ)*n) z) atTop
      (𝓝 (-2*Complex.sin z)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he := (Complex.tendsto_euler_sin_prod (z/(Real.pi : ℂ))).const_mul (-2)
  convert he using 1
  · funext N
    rw [singleSpectralPartialProduct_free_eq]
    rw [mul_div_cancel₀ _ hpi, ← mul_assoc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [div_pow, mul_pow, div_div]
  · rw [mul_div_cancel₀ _ hpi]

/-- A single normalized factor splits into its free and relative factors. -/
theorem singleSpectralFactor_eq_free_mul_relative (ξ : ℤ → ℂ) (z : ℂ)
    (hz : z ∉ freeLattice) (n : ℤ) :
    singleSpectralFactor ξ z n =
      singleSpectralFactor (fun n => (Real.pi : ℂ)*n) z n * spectralRelativeFactor ξ z n := by
  have hd : (Real.pi : ℂ)*n-z ≠ 0 := by
    simpa only [sub_ne_zero] using (sub_ne_zero.mp (free_denominator_ne_zero hz n)).symm
  unfold singleSpectralFactor spectralRelativeFactor
  field_simp

/-- The relative decomposition preserves the literal symmetric cutoff. -/
theorem singleSpectralPartialProduct_eq (ξ : ℤ → ℂ) (z : ℂ)
    (hz : z ∉ freeLattice) (N : ℕ) :
    singleSpectralPartialProduct ξ z N =
      singleSpectralPartialProduct (fun n => (Real.pi : ℂ)*n) z N *
        ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralRelativeFactor ξ z n := by
  simp only [singleSpectralPartialProduct, singleSpectralFactor_eq_free_mul_relative ξ z hz,
    Finset.prod_mul_distrib, mul_assoc]

end NLS.ZakharovShabat
