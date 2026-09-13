import NLS.ZakharovShabat.FreeSpectralProductsUniform
import NLS.ZakharovShabat.SpectralProductSourceAudit

/-!
# Correctly normalized free parity products

The odd cutoff uses the literal indices `2n+1` for `-N ≤ n ≤ N`. Translation
of the even lattice and division by a fixed reference product preserves that
asymmetric cutoff exactly, including its exceptional central denominator.
-/

noncomputable section
open Filter Topology
namespace NLS.ZakharovShabat

/-- The half-lattice reference factors never vanish. -/
theorem freeSpectralFactor_halfShift_ne_zero (h : ℂ) (hh : h ≠ 0) (n : ℤ) :
    freeSpectralFactor (2*h) (-h) n ≠ 0 := by
  have hodd : (2*(n : ℂ)+1) ≠ 0 := by
    exact_mod_cast (show (2*n+1 : ℤ) ≠ 0 by omega)
  by_cases hn : n = 0
  · simp [hn, hh]
  · unfold freeSpectralFactor
    rw [if_neg hn]
    apply pow_ne_zero
    apply div_ne_zero
    · rw [show 2*h*(n : ℂ)- -h = h*(2*n+1) by ring]
      exact mul_ne_zero hh hodd
    · exact mul_ne_zero (mul_ne_zero two_ne_zero hh) (Int.cast_ne_zero.mpr hn)

/-- Every odd factor is a translated even factor divided by its nonzero reference value. -/
theorem freeSpectralFactor_odd_eq_quotient (h z : ℂ) (hh : h ≠ 0) (n : ℤ) :
    freeSpectralFactor h z (2*n+1) =
      freeSpectralFactor (2*h) (z-h) n / freeSpectralFactor (2*h) (-h) n := by
  have hodd : (2*(n : ℂ)+1) ≠ 0 := by
    exact_mod_cast (show (2*n+1 : ℤ) ≠ 0 by omega)
  have hi : (2*n+1 : ℤ) ≠ 0 := by omega
  by_cases hn : n = 0
  · subst n
    norm_num [freeSpectralFactor]
    field_simp
    ring
  · simp only [freeSpectralFactor, if_neg hi, if_neg hn]
    push_cast
    have hd : 2*h*(n : ℂ)+h ≠ 0 := by
      rw [show 2*h*(n : ℂ)+h = h*(2*n+1) by ring]
      exact mul_ne_zero hh hodd
    have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    rw [show 2*h*(n : ℂ)- -h = h*(2*n+1) by ring]
    field_simp [hh, hn', hodd]
    ring

/-- The entire half-lattice reference product is nonzero at every finite cutoff. -/
theorem freeSpectralPartialProduct_halfShift_ne_zero (h : ℂ) (hh : h ≠ 0) (N : ℕ) :
    freeSpectralPartialProduct (2*h) (-h) N ≠ 0 := by
  rw [freeSpectralPartialProduct_eq_prod_Icc]
  exact Finset.prod_ne_zero_iff.mpr (fun n _ => freeSpectralFactor_halfShift_ne_zero h hh n)

/-- Correctly normalized literal antiperiodic cutoffs. -/
def freeAntiperiodicProduct (z : ℂ) (N : ℕ) : ℂ :=
  4 * ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), freeSpectralFactor (Real.pi : ℂ) z (2*n+1)

/-- The odd cutoff is exactly a ratio of translated even products. -/
theorem freeAntiperiodicProduct_eq_quotient (z : ℂ) (N : ℕ) :
    freeAntiperiodicProduct z N =
      4*freeSpectralPartialProduct (2*(Real.pi : ℂ)) (z-(Real.pi : ℂ)) N /
        freeSpectralPartialProduct (2*(Real.pi : ℂ)) (-(Real.pi : ℂ)) N := by
  simp only [freeAntiperiodicProduct, freeSpectralFactor_odd_eq_quotient _ _
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), Finset.prod_div_distrib,
    freeSpectralPartialProduct_eq_prod_Icc, mul_div_assoc]

/-- The denominator in the translated odd product tends to four. -/
theorem tendsto_freeParityReference :
    Tendsto (freeSpectralPartialProduct (2*(Real.pi : ℂ)) (-(Real.pi : ℂ))) atTop (𝓝 4) := by
  have h := (tendsto_freePeriodOneProduct (-(Real.pi : ℂ))).neg
  convert h using 1 <;> norm_num [freeDiscriminant]

/-- The free odd product has the required limit with prefactor four, including at all lattice points. -/
theorem tendsto_freeAntiperiodicProduct (z : ℂ) :
    Tendsto (freeAntiperiodicProduct z) atTop (𝓝 (freeDiscriminant z+2)) := by
  have h := ((tendsto_freePeriodOneProduct (z-(Real.pi : ℂ))).neg.const_mul 4).div
    tendsto_freeParityReference (by norm_num)
  have he : 4 * -(freeDiscriminant (z-(Real.pi : ℂ))-2)/4 = freeDiscriminant z+2 := by
    simp [freeDiscriminant, Complex.cos_sub]
    ring
  change Tendsto (fun N => 4 * -(-freeSpectralPartialProduct (2*(Real.pi : ℂ))
    (z-(Real.pi : ℂ)) N) / freeSpectralPartialProduct (2*(Real.pi : ℂ)) (-(Real.pi : ℂ)) N)
    atTop (𝓝 _) at h
  simpa only [neg_neg, ← freeAntiperiodicProduct_eq_quotient, he] using h

/-- The translated odd cutoffs converge locally uniformly on the whole spectral plane. -/
theorem tendstoLocallyUniformlyOn_freeAntiperiodicProduct :
    TendstoLocallyUniformlyOn (fun N z => freeAntiperiodicProduct z N)
      (fun z => freeDiscriminant z+2) atTop Set.univ := by
  have hfree := (tendstoLocallyUniformlyOn_freeSpectralPartialProduct (2*(Real.pi : ℂ))
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).comp (t := Set.univ)
      (fun z : ℂ => z-(Real.pi : ℂ)) (fun _ _ => Set.mem_univ _) (by fun_prop)
  have hc := ((tendsto_const_nhds (x := (4 : ℂ))).div tendsto_freeParityReference (by norm_num : (4 : ℂ) ≠ 0)).tendstoUniformlyOn_const
    (Set.univ : Set ℂ)
  have h := hc.tendstoLocallyUniformlyOn.mul₀ hfree continuousOn_const (by fun_prop)
  have hp : TendstoLocallyUniformlyOn (fun N z => freeAntiperiodicProduct z N)
      (fun z => (4/4 : ℂ)*((2*(Real.pi : ℂ))/(Real.pi : ℂ)*
        Complex.sin ((Real.pi : ℂ)*(z-(Real.pi : ℂ))/(2*(Real.pi : ℂ))))^2) atTop Set.univ := by
    apply h.congr
    intro N z _
    dsimp only [Pi.mul_apply, Pi.div_apply, Function.comp_def]
    rw [freeAntiperiodicProduct_eq_quotient]
    ring
  exact hp.congr_right (fun z _ => tendsto_nhds_unique (hp.tendsto_at (Set.mem_univ z))
    (tendsto_freeAntiperiodicProduct z))

end NLS.ZakharovShabat
