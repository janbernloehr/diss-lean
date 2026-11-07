import NLS.ZakharovShabat.EntireSingleSpectralProducts

/-! Exact pairing and parity of full single spectral products for a
balanced root sequence. Literal symmetric finite cutoffs are retained. -/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem singleSpectralPartialProduct_eq_of_balanced (ρ : ℤ → ℂ)
    (hzero : ρ 0 = 0) (hneg : ∀ k : ℤ, ρ (-k) = -ρ k) (z : ℂ) (N : ℕ) :
    singleSpectralPartialProduct ρ z N =
      -2*z*∏ j ∈ Finset.range N, ((ρ ((j:ℤ)+1))^2-z^2)/((Real.pi:ℂ)*((j:ℂ)+1))^2 := by
  rw [singleSpectralPartialProduct,prod_symmetric_interval]
  have hp (j : ℕ) : singleSpectralFactor ρ z ((j:ℤ)+1)*singleSpectralFactor ρ z (-((j:ℤ)+1)) =
      ((ρ ((j:ℤ)+1))^2-z^2)/((Real.pi:ℂ)*((j:ℂ)+1))^2 := by
    simp only [singleSpectralFactor,singleSpectralDenominator,
      if_neg (by omega : (j:ℤ)+1 ≠ 0),if_neg (by omega : -((j:ℤ)+1) ≠ 0),hneg]
    push_cast
    have hj : (j:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero j
    have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  simp only [hp]
  simp only [singleSpectralFactor,singleSpectralDenominator,hzero,
    zero_sub,↓reduceIte,div_one]
  ring

theorem singleSpectralPartialProduct_neg_of_balanced (ρ : ℤ → ℂ)
    (hzero : ρ 0 = 0) (hneg : ∀ k : ℤ, ρ (-k) = -ρ k) (z : ℂ) (N : ℕ) :
    singleSpectralPartialProduct ρ (-z) N = -singleSpectralPartialProduct ρ z N := by
  rw [singleSpectralPartialProduct_eq_of_balanced ρ hzero hneg,
    singleSpectralPartialProduct_eq_of_balanced ρ hzero hneg]
  simp only [neg_sq]
  ring

theorem entireSingleSpectralProduct_neg_of_balanced
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (ρ : ℤ → ℂ)
    (hρ : Memℓp (fun k => ρ k-(Real.pi:ℂ)*k) p)
    (hzero : ρ 0 = 0) (hneg : ∀ k : ℤ, ρ (-k) = -ρ k) (z : ℂ) :
    entireSingleSpectralProduct ρ (-z) = -entireSingleSpectralProduct ρ z := by
  have ht := ((tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp ρ hρ).tendsto_at (mem_univ z)).neg
  have ht' := (tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp ρ hρ).tendsto_at (mem_univ (-z))
  simp_rw [singleSpectralPartialProduct_neg_of_balanced ρ hzero hneg] at ht'
  exact tendsto_nhds_unique ht' ht

end NLS.ZakharovShabat
