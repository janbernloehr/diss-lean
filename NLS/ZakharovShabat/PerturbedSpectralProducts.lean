import NLS.ZakharovShabat.RelativeSpectralProducts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Symmetric products of perturbed spectral pairs

The factors use the original eigenvalues and the exceptional denominator one
at the zero mode. Their symmetric cutoffs converge away from the free lattice
by the free Euler product and the absolutely convergent relative product.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source's normalized two-root factor, including its exceptional zero denominator. -/
def spectralPairFactor (ξ η : ℤ → ℂ) (z : ℂ) (n : ℤ) : ℂ :=
  if n = 0 then (ξ n-z)*(η n-z) else (ξ n-z)*(η n-z)/((Real.pi : ℂ)*n)^2

/-- The full periodic partial product in equation (2.1). -/
def spectralPairPartialProduct (ξ η : ℤ → ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  -4 * ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralPairFactor ξ η z n

/-- Each original factor splits into its free factor and the two relative factors. -/
theorem spectralPairFactor_eq_free_mul_relative (ξ η : ℤ → ℂ) (z : ℂ)
    (hz : z ∉ freeLattice) (n : ℤ) :
    spectralPairFactor ξ η z n = freeSpectralFactor (Real.pi : ℂ) z n *
      (spectralRelativeFactor ξ z n * spectralRelativeFactor η z n) := by
  have hd : (Real.pi : ℂ)*n-z ≠ 0 := by
    simpa only [sub_ne_zero] using (sub_ne_zero.mp (free_denominator_ne_zero hz n)).symm
  by_cases hn : n = 0
  · subst n
    have hz0 : z ≠ 0 := by simpa using hd
    simp only [spectralPairFactor, freeSpectralFactor, spectralRelativeFactor,
      Int.cast_zero, mul_zero, zero_sub, ↓reduceIte]
    field_simp
  · have hden : (Real.pi : ℂ)*n ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (Int.cast_ne_zero.mpr hn)
    simp only [spectralPairFactor, freeSpectralFactor, if_neg hn, spectralRelativeFactor]
    field_simp

/-- The decomposition respects the literal symmetric cutoff. -/
theorem spectralPairPartialProduct_eq (ξ η : ℤ → ℂ) (z : ℂ) (hz : z ∉ freeLattice) (N : ℕ) :
    spectralPairPartialProduct ξ η z N = (-4 * freeSpectralPartialProduct (Real.pi : ℂ) z N) *
      ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (spectralRelativeFactor ξ z n * spectralRelativeFactor η z n) := by
  simp only [spectralPairPartialProduct, spectralPairFactor_eq_free_mul_relative ξ η z hz,
    Finset.prod_mul_distrib, freeSpectralPartialProduct_eq_prod_Icc, mul_assoc]

/-- The convergent value on the complement of the free lattice; extension across that lattice is separate. -/
def spectralPairProductOffLattice (ξ η : ℤ → ℂ) (z : {z : ℂ // z ∉ freeLattice}) : ℂ :=
  ((freeDiscriminant z.val)^2-4) * spectralRelativePairProduct ξ η z.val

/-- Every finite-exponent displacement pair gives a convergent source product away from the free lattice. -/
theorem tendsto_spectralPairPartialProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    Tendsto (spectralPairPartialProduct ξ η z) atTop (𝓝 (spectralPairProductOffLattice ξ η ⟨z,hz⟩)) := by
  have h := (tendsto_freePeriodicFullProduct z).mul (tendsto_spectralRelativePairProduct hp ξ η hξ hη z hz)
  exact h.congr (fun N => (spectralPairPartialProduct_eq ξ η z hz N).symm)

/-- The free normalizing factor cannot add zeros off its lattice. -/
theorem freeDiscriminant_sq_sub_four_ne_zero (z : ℂ) (hz : z ∉ freeLattice) :
    (freeDiscriminant z)^2-4 ≠ 0 := by
  have hs : Complex.sin z ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp h
    exact hz ⟨n, by simpa only [mul_comm] using hn.symm⟩
  have he : (freeDiscriminant z)^2-4 = -4*(Complex.sin z)^2 := by
    have h := Complex.sin_sq_add_cos_sq z
    unfold freeDiscriminant
    linear_combination 4*h
  rw [he]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hs)

/-- Off the free lattice the convergent source product has exactly the selected zeros. -/
theorem spectralPairProductOffLattice_eq_zero_iff (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    spectralPairProductOffLattice ξ η ⟨z,hz⟩ = 0 ↔ ∃ n : ℤ, ξ n = z ∨ η n = z := by
  rw [spectralPairProductOffLattice, mul_eq_zero]
  simp only [freeDiscriminant_sq_sub_four_ne_zero z hz, false_or]
  exact spectralRelativePairProduct_eq_zero_iff hp ξ η hξ hη z hz

end NLS.ZakharovShabat
