import NLS.KdV.HillFreeActionGapRatio
import NLS.KdV.HillActionGapPrefactor
import NLS.KdV.HillSummedRegularCorrection

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The original positive own-amplitude prefactor at every free gap. -/
theorem hillActionGapPrefactor_free_value (n : ℕ) (hn : 1 ≤ n) :
    hillActionGapPrefactor 0 h0q h0r n = (Real.sqrt ((n : ℝ)*Real.pi) : ℂ)⁻¹ := by
  have he : hillActionGapRatio 0 h0q h0r n = (((2*(n : ℝ)*Real.pi)⁻¹ : ℝ) : ℂ) := by
    rw [hillActionGapRatio_zero h0q h0r n hn]
    simp only [ofReal_inv,ofReal_mul,ofReal_ofNat,ofReal_natCast]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hi : 2*(2*(n : ℝ)*Real.pi)⁻¹ = ((n : ℝ)*Real.pi)⁻¹ := by
    field_simp [hn0,Real.pi_ne_zero]
  rw [hillActionGapPrefactor,he,ofReal_re,hi,Real.sqrt_inv,ofReal_inv]

/-- The exact original base sequence normalization times the original
free action-gap prefactor equals sqrt(2), with positive real sign. -/
theorem hillActionGapPrefactor_free_base_normalization (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt (2*Real.pi*(n : ℝ)) : ℂ)*hillActionGapPrefactor 0 h0q h0r n = (Real.sqrt 2 : ℂ) := by
  have hp : 0 < (n : ℝ)*Real.pi := mul_pos (by exact_mod_cast (by omega : 0 < n)) Real.pi_pos
  have hs : (Real.sqrt ((n : ℝ)*Real.pi) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp).ne'
  rw [hillActionGapPrefactor_free_value h0q h0r n hn,
    show 2*Real.pi*(n : ℝ) = 2*((n : ℝ)*Real.pi) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),ofReal_mul,mul_assoc,mul_inv_cancel₀ hs,mul_one]

/-- The ENTIRE original regular correction, including its own term and
all off-index terms, vanishes at the free potential. -/
theorem hillSummedRegularAbelianCorrection_free (n : ℕ) (hn : 1 ≤ n) :
    hillSummedRegularAbelianCorrection 0 h0q h0r n hn = 0 := by
  have hgap (k : ℕ) (hk : 1 ≤ k) : hillRealGapHalfLength 0 h0q h0r k = 0 := by
    obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r k hk
    rw [hillRealGapHalfLength,hl,hu,sub_self,zero_div]
  unfold hillSummedRegularAbelianCorrection
  have hz (k : ℕ) : hillRegularAbelianCorrection 0 h0q h0r n hn (k+1) (by omega) = 0 :=
    hillRegularAbelianCorrection_closed 0 h0q h0r n hn (k+1) (by omega) (hgap _ (by omega))
  simp only [hz,tsum_zero]

/-- The complete REGULAR correction multiplier at the free source is one.
The original Dirichlet-circle phase is already in the own amplitude. -/
theorem hillRegularCorrectionPhaseMultiplier_free (n : ℕ) (hn : 1 ≤ n) :
    Complex.exp (I*hillSummedRegularAbelianCorrection 0 h0q h0r n hn) = 1 := by
  rw [hillSummedRegularAbelianCorrection_free h0q h0r n hn,mul_zero,Complex.exp_zero]

end NLS.KdV
