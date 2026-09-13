import NLS.ZakharovShabat.FreeSpectralProducts

/-!
# The prefactor inconsistency in equation (2.4) and Lemma 8.1

Printed page 48 uses `-2` for the periodic product and `2` for the
antiperiodic product. At the actual zero potential and spectral parameter zero,
these give `f+2=2` and `g-2=0`. Thus the displayed compatibility assertion is
false. The proof on the same page instead uses the necessary periodic prefactor
`-1`; the antiperiodic prefactor is forced to be `4` by the free value at zero.
-/

noncomputable section
open Filter Topology
namespace NLS.ZakharovShabat

/-- The literal periodic prefactor in (2.4), with the actual doubled free even eigenvalues. -/
def printedFreePeriodicProduct (z : ℂ) (N : ℕ) : ℂ :=
  -2 * freeSpectralPartialProduct (2*(Real.pi : ℂ)) z N

/-- The periodic expression is the literal symmetric cutoff over the even free spectrum. -/
theorem printedFreePeriodicProduct_eq (z : ℂ) (N : ℕ) :
    printedFreePeriodicProduct z N =
      -2 * ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), freeSpectralFactor (Real.pi : ℂ) z (2*n) := by
  simp only [printedFreePeriodicProduct, freeSpectralPartialProduct_eq_prod_Icc, freeSpectralFactor_even]

/-- The literal antiperiodic prefactor in (2.4), with actual doubled free odd eigenvalues. -/
def printedFreeAntiperiodicProduct (z : ℂ) (N : ℕ) : ℂ :=
  2 * ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), freeSpectralFactor (Real.pi : ℂ) z (2*n+1)

@[simp] theorem printedFreePeriodicProduct_zero (N : ℕ) : printedFreePeriodicProduct 0 N = 0 := by
  simp [printedFreePeriodicProduct, freeSpectralPartialProduct]

/-- Every odd free factor is one at zero; this uses no choice of limit convention. -/
@[simp] theorem freeSpectralFactor_odd_zero (n : ℤ) : freeSpectralFactor (Real.pi : ℂ) 0 (2*n+1) = 1 := by
  have hn : (2*n+1 : ℤ) ≠ 0 := by omega
  have hd : (Real.pi : ℂ)*(2*n+1 : ℤ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (Int.cast_ne_zero.mpr hn)
  simp only [freeSpectralFactor, if_neg hn, sub_zero, div_self hd, one_pow]

@[simp] theorem printedFreeAntiperiodicProduct_zero (N : ℕ) : printedFreeAntiperiodicProduct 0 N = 2 := by
  simp [printedFreeAntiperiodicProduct]

/-- The two printed expressions already disagree at every finite cutoff at the origin. -/
theorem printedFreeProducts_incompatible (N : ℕ) :
    printedFreePeriodicProduct 0 N + 2 ≠ printedFreeAntiperiodicProduct 0 N - 2 := by simp

/-- No discriminant value can satisfy both displayed product limits in Lemma 8.1(ii). -/
theorem not_exists_discriminant_value_for_printed_products :
    ¬∃ Δ : ℂ, Tendsto (printedFreePeriodicProduct 0) atTop (𝓝 (Δ-2)) ∧
      Tendsto (printedFreeAntiperiodicProduct 0) atTop (𝓝 (Δ+2)) := by
  rintro ⟨Δ, hf, hg⟩
  have hf0 : Tendsto (printedFreePeriodicProduct 0) atTop (𝓝 0) := by
    rw [show printedFreePeriodicProduct 0 = (fun _ : ℕ => (0 : ℂ)) from funext printedFreePeriodicProduct_zero]
    exact tendsto_const_nhds
  have hg2 : Tendsto (printedFreeAntiperiodicProduct 0) atTop (𝓝 2) := by
    rw [show printedFreeAntiperiodicProduct 0 = (fun _ : ℕ => (2 : ℂ)) from funext printedFreeAntiperiodicProduct_zero]
    exact tendsto_const_nhds
  have h₁ := tendsto_nhds_unique hf hf0
  have h₂ := tendsto_nhds_unique hg hg2
  have h : (4 : ℂ) = 2 := by linear_combination h₂ - h₁
  norm_num at h

/-- The literal periodic product converges, but to twice the required free expression. -/
theorem tendsto_printedFreePeriodicProduct (z : ℂ) :
    Tendsto (printedFreePeriodicProduct z) atTop (𝓝 (2*(freeDiscriminant z-2))) := by
  have h := (tendsto_freePeriodOneProduct z).const_mul 2
  convert h using 1
  funext N
  simp [printedFreePeriodicProduct]

/-- The printed periodic prefactor fails at the nonzero parameter π as well. -/
theorem printedFreePeriodicProduct_wrong_at_pi :
    ¬Tendsto (printedFreePeriodicProduct (Real.pi : ℂ)) atTop
      (𝓝 (freeDiscriminant (Real.pi : ℂ)-2)) := by
  intro h
  have he := tendsto_nhds_unique h (tendsto_printedFreePeriodicProduct (Real.pi : ℂ))
  norm_num [freeDiscriminant] at he

/-- Any antiperiodic prefactor compatible with the free discriminant at zero must be four. -/
theorem freeAntiperiodic_prefactor_eq_four (c : ℂ)
    (hc : Tendsto (fun N : ℕ => c * ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      freeSpectralFactor (Real.pi : ℂ) 0 (2*n+1)) atTop (𝓝 (freeDiscriminant 0+2))) : c = 4 := by
  have hconst : Tendsto (fun N : ℕ => c * ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      freeSpectralFactor (Real.pi : ℂ) 0 (2*n+1)) atTop (𝓝 c) := by simp
  have he := tendsto_nhds_unique hconst hc
  norm_num [freeDiscriminant] at he
  exact he

/-- Any periodic prefactor compatible with the free discriminant at π must be minus one. -/
theorem freePeriodOne_prefactor_eq_neg_one (c : ℂ)
    (hc : Tendsto (fun N : ℕ => c * freeSpectralPartialProduct (2*(Real.pi : ℂ)) (Real.pi : ℂ) N)
      atTop (𝓝 (freeDiscriminant (Real.pi : ℂ)-2))) : c = -1 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (tendsto_freeSpectralPartialProduct (2*(Real.pi : ℂ)) (Real.pi : ℂ)
    (mul_ne_zero two_ne_zero hpi)).const_mul c
  have ha : (2*(Real.pi : ℂ))/(Real.pi : ℂ) = 2 := mul_div_cancel_right₀ 2 hpi
  have hb : (Real.pi : ℂ)*(Real.pi : ℂ)/(2*(Real.pi : ℂ)) = (Real.pi : ℂ)/2 := by field_simp
  have he := tendsto_nhds_unique h hc
  rw [ha, hb] at he
  norm_num [freeDiscriminant] at he
  linear_combination he / 4

end NLS.ZakharovShabat
