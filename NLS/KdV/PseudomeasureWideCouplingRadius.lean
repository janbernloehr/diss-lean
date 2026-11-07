import NLS.KdV.PseudomeasureWideZeroCount
import NLS.KdV.PseudomeasureRootSeparation

/-! The literal full-wide-strip coupling supremum and the sharp sqrt(6)
separation estimate for the same actual determinant. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV

theorem endpointEffectiveFamily_eq_wide (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 2≤n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ wideHillStrip n)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    endpointEffectiveFamily r hr hr1 n p=
      wideEndpointHillEffectivePotential r hr hr1 n hn p.2 hz p.1 hs := by
  unfold endpointEffectiveFamily wideEndpointHillEffectivePotential
  rw [endpointInverseFamily_eq_wide r hr hr1 n hn p hz hs,endpointModePotentialFamily_eq]

variable (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (hn : 2≤n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

include hn hs in
theorem sqrt_endpointCouplingProduct_le_weight_norm_wide (z : ℂ) (hz : z ∈ wideHillStrip n) :
    Real.sqrt ‖endpointUpperCoupling r hr hr1 n (q,z)*endpointLowerCoupling r hr hr1 n (q,z)‖ ≤
      2*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
  have hW := ((Weight.sobolev r).positive (2*(n:ℤ))).le
  have h1 := (wideEndpointHillEffectiveCorrection_columns_le r hr hr1 n hn z hz q hs).1
  have h2 := (wideEndpointHillEffectiveCorrection_columns_le r hr hr1 n hn z hz q hs).2
  have hplus : ‖endpointUpperCoupling r hr hr1 n (q,z)‖ ≤
      2*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
    unfold endpointUpperCoupling
    rw [endpointEffectiveFamily_eq_wide r hr hr1 n hn (q,z) hz hs]
    exact (norm_fst_le _).trans h2
  have hminus : ‖endpointLowerCoupling r hr hr1 n (q,z)‖ ≤
      2*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
    unfold endpointLowerCoupling
    rw [endpointEffectiveFamily_eq_wide r hr hr1 n hn (q,z) hz hs]
    exact (norm_snd_le _).trans h1
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) ((Weight.sobolev r).positive _).le) (norm_nonneg q), ?_⟩
  rw [norm_mul, pow_two]
  exact mul_le_mul hplus hminus (norm_nonneg _) (by positivity)

/-- The same actual coupling product, with supremum over the full printed strip. -/
def wideEndpointCouplingRadius : ℝ :=
  sSup ((fun z : ℂ => Real.sqrt ‖endpointUpperCoupling r hr hr1 n (q,z)*
    endpointLowerCoupling r hr hr1 n (q,z)‖) '' wideHillStrip n)

include hn hs in
theorem bddAbove_wideEndpointCouplingRadii :
    BddAbove ((fun z : ℂ => Real.sqrt ‖endpointUpperCoupling r hr hr1 n (q,z)*
      endpointLowerCoupling r hr hr1 n (q,z)‖) '' wideHillStrip n) := by
  refine ⟨2*Weight.sobolev r (2*(n:ℤ))*‖q‖,?_⟩
  rintro _ ⟨z,hz,rfl⟩
  exact sqrt_endpointCouplingProduct_le_weight_norm_wide r hr hr1 n hn q hs z hz

include hn hs in
theorem endpointCouplingRadius_le_wide :
    endpointCouplingRadius r hr hr1 n q ≤ wideEndpointCouplingRadius r hr hr1 n q := by
  apply csSup_le_csSup (bddAbove_wideEndpointCouplingRadii r hr hr1 n hn q hs)
  · exact ⟨_,⟨wideHillCenter n 0,wideHillCenter_mem n 0,rfl⟩⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact ⟨z,reducedHillStrip_subset_wide n hz,rfl⟩

include hn hs in
theorem endpointReduced_roots_separation_sqrt_wide (z y : ℂ)
    (hz : z ∈ wideHillStrip n) (hy : y ∈ wideHillStrip n)
    (hdz : endpointReducedDeterminant r hr hr1 n (q,z)=0)
    (hdy : endpointReducedDeterminant r hr hr1 n (q,y)=0) :
    ‖z-y‖ ≤ Real.sqrt 6*wideEndpointCouplingRadius r hr hr1 n q := by
  have hzN := (endpointReducedDeterminant_wide_zero_localization r hr hr1 n hn q hs z hz hdz).1
  have hyN := (endpointReducedDeterminant_wide_zero_localization r hr hr1 n hn q hs y hy hdy).1
  exact (endpointReduced_roots_separation_sqrt r hr hr1 n (by omega) q
    (endpointHill_small_of_wide_small r hr1 n q hs) z y hzN hyN hdz hdy).trans
      (mul_le_mul_of_nonneg_left (endpointCouplingRadius_le_wide r hr hr1 n hn q hs) (Real.sqrt_nonneg _))

end NLS.KdV
