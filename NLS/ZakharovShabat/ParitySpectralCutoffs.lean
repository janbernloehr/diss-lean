import NLS.ZakharovShabat.FreeParityProducts
import NLS.ZakharovShabat.EntireSpectralPairProducts

/-!
# Exact parity cutoff identities

Affine reindexing sends each parity lattice back to `πℤ`. The even zero mode
and the odd reference denominator fix the respective prefactors `-1` and `4`.
All identities hold at finite cutoffs, including coincident or vanishing roots.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reindex a parity and normalize its spacing and origin to the standard free lattice. -/
def parityRescale (ξ : ℤ → ℂ) (j : ℤ) (n : ℤ) : ℂ :=
  (ξ (2*n+j)-(Real.pi : ℂ)*j)/2

/-- Reindexing and rescaling preserve summable-power spectral displacements. -/
theorem memℓp_parityRescale (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (j : ℤ) :
    Memℓp (fun n => parityRescale ξ j n-(Real.pi : ℂ)*n) p := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne' hp
  have hs : Memℓp (fun n : ℤ => ξ (2*n+j)-(Real.pi : ℂ)*((2*n+j : ℤ) : ℂ)) p := by
    rw [memℓp_gen_iff hp0]
    exact (hξ.summable hp0).comp_injective (i := fun n : ℤ => 2*n+j) (show Function.Injective (fun n : ℤ => 2*n+j) by
      intro a b hab; dsimp at hab; omega)
  have he : (fun n => parityRescale ξ j n-(Real.pi : ℂ)*n) =
      fun n : ℤ => (2 : ℂ)⁻¹*(ξ (2*n+j)-(Real.pi : ℂ)*((2*n+j : ℤ) : ℂ)) := by
    funext n
    unfold parityRescale
    push_cast
    ring
  rw [he]
  exact hs.const_mul _

/-- Correctly normalized even partial products, with the original zero-mode denominator. -/
def evenSpectralPairCutoff (ξ η : ℤ → ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  -∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralPairFactor ξ η z (2*n)

/-- Correctly normalized odd partial products with the literal asymmetric odd cutoff. -/
def oddSpectralPairCutoff (ξ η : ℤ → ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  4*∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralPairFactor ξ η z (2*n+1)

/-- Even rescaling produces one factor of four exactly at the central mode. -/
theorem spectralPairFactor_even_eq (ξ η : ℤ → ℂ) (z : ℂ) (n : ℤ) :
    spectralPairFactor ξ η z (2*n) = (if n = 0 then 4 else 1)*
      spectralPairFactor (parityRescale ξ 0) (parityRescale η 0) (z/2) n := by
  by_cases hn : n = 0
  · subst n
    simp [spectralPairFactor, parityRescale]
    ring
  · simp only [spectralPairFactor, if_neg hn, if_neg (by omega : 2*n ≠ 0), one_mul, parityRescale]
    push_cast
    simp only [mul_zero, sub_zero, add_zero]
    field_simp

/-- The even cutoff is exactly a standard full product for the rescaled sequences. -/
theorem evenSpectralPairCutoff_eq (ξ η : ℤ → ℂ) (z : ℂ) (N : ℕ) :
    evenSpectralPairCutoff ξ η z N =
      spectralPairPartialProduct (parityRescale ξ 0) (parityRescale η 0) (z/2) N := by
  simp only [evenSpectralPairCutoff, spectralPairFactor_even_eq, Finset.prod_mul_distrib,
    spectralPairPartialProduct]
  have he : (∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (if n = 0 then (4 : ℂ) else 1)) = 4 := by
    simp
  rw [he]
  ring

/-- Odd rescaling divides by the half-step reference factor, including at its central mode. -/
theorem spectralPairFactor_odd_eq (ξ η : ℤ → ℂ) (z : ℂ) (n : ℤ) :
    spectralPairFactor ξ η z (2*n+1) =
      spectralPairFactor (parityRescale ξ 1) (parityRescale η 1) ((z-(Real.pi : ℂ))/2) n /
        freeSpectralFactor (Real.pi : ℂ) (-(Real.pi : ℂ)/2) n := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hodd : (2*(n : ℂ)+1) ≠ 0 := by exact_mod_cast (show (2*n+1 : ℤ) ≠ 0 by omega)
  by_cases hn : n = 0
  · subst n
    norm_num [spectralPairFactor, freeSpectralFactor, parityRescale]
    field_simp
    ring
  · simp only [spectralPairFactor, freeSpectralFactor, if_neg hn,
      if_neg (by omega : 2*n+1 ≠ 0), parityRescale]
    push_cast
    simp only [mul_one]
    have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    rw [show (Real.pi : ℂ)*(n : ℂ)- -(Real.pi : ℂ)/2 = (Real.pi : ℂ)*(2*n+1)/2 by ring]
    field_simp [hpi, hn', hodd]
    ring

/-- The odd cutoff is exactly the negative rescaled full product divided by a nonzero reference product. -/
theorem oddSpectralPairCutoff_eq (ξ η : ℤ → ℂ) (z : ℂ) (N : ℕ) :
    oddSpectralPairCutoff ξ η z N =
      -spectralPairPartialProduct (parityRescale ξ 1) (parityRescale η 1) ((z-(Real.pi : ℂ))/2) N /
        freeSpectralPartialProduct (Real.pi : ℂ) (-(Real.pi : ℂ)/2) N := by
  simp only [oddSpectralPairCutoff, spectralPairFactor_odd_eq, Finset.prod_div_distrib,
    spectralPairPartialProduct, freeSpectralPartialProduct_eq_prod_Icc]
  ring

/-- The rescaled odd reference tends to one, fixing its normalization. -/
theorem tendsto_rescaledOddReference :
    Tendsto (freeSpectralPartialProduct (Real.pi : ℂ) (-(Real.pi : ℂ)/2)) atTop (𝓝 1) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := tendsto_freeSpectralPartialProduct (Real.pi : ℂ) (-(Real.pi : ℂ)/2) hpi
  have he : (Real.pi : ℂ)*(-(Real.pi : ℂ)/2)/(Real.pi : ℂ) = -(Real.pi : ℂ)/2 := by field_simp
  simpa [div_self hpi, he, neg_div, Complex.sin_neg] using h

end NLS.ZakharovShabat
