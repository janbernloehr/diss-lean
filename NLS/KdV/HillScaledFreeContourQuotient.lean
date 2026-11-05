import NLS.KdV.HillFreeContourSeparation
import NLS.KdV.HillFreeAbelianQuotient

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGapContour_scaled_resolvent_bound (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hnk : n ≠ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) :
    ‖((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/((freeHillValue n : ℂ)-E)‖ ≤ 2 := by
  have hsep := hillFreeGapContour_energy_separation hq hr k hk (n : ℤ)
    (by exact_mod_cast hnk) (by exact_mod_cast (show 0 < n by omega)) E hE
  have hne : (freeHillValue n : ℂ) ≠ (freeHillValue k : ℂ) := by
    exact_mod_cast (strictMono_freeHillValue.injective.ne hnk)
  have hpos : 0 < ‖(freeHillValue n : ℂ)-(freeHillValue k : ℂ)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hden : 0 < ‖(freeHillValue n : ℂ)-E‖ := by linarith only [hsep,hpos]
  rw [norm_div,norm_sub_rev (freeHillValue k : ℂ) (freeHillValue n : ℂ)]
  apply (div_le_iff₀ hden).mpr
  linarith only [hsep]

theorem norm_scaled_hillFreeAbelianQuotient_on_contour (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hnk : n ≠ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) :
    ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianPsiCandidate hillFreeGapRoot n E/hillEnergyCanonicalRootProduct 0 hq hr E)‖ ≤
      4/(k : ℝ) := by
  rw [hillFreeAbelianQuotient hq hr n hn E (hillRealGapContour_sphere_subset 0 hq hr k hk hE)]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (I*((n : ℂ)*Real.pi)/(Complex.sqrt E*((freeHillValue n : ℂ)-E))) =
      (I*Real.pi)*(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/((freeHillValue n : ℂ)-E))/Complex.sqrt E := by
    field_simp
  rw [he,norm_div,norm_mul,norm_mul,norm_I,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul]
  have hb := hillFreeGapContour_scaled_resolvent_bound hq hr n k hn hk hnk E hE
  have hg := hillFreeGapContour_frequency_bounds hq hr k hk E hE
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb Real.pi_pos.le) (norm_nonneg _)).trans
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity : (0 : ℝ) < (k : ℝ)*Real.pi/2) hg.2.2.2).trans_eq
  field_simp
  norm_num

end NLS.KdV
