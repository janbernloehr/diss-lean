import NLS.KdV.HillMeanZeroTraceVariationBound
import NLS.KdV.HillGapProductInverseFreeBound
import NLS.ZakharovShabat.FreeSineExteriorBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- Actual mean-zero trace variations decay relative to every original
full gap product on the expanding central energy circles. -/
theorem eventually_hillMeanZeroTraceVariation_div_full_product_le
    (q : RealPeriodOneHillPotential) (p h : Coeff 2) (hzero : h 0 = 0)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q.val q.property.1 q.property.2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖((fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant (Coeff.periodDouble a) E) p) h)/
        hillAbelianNumeratorProduct roots 0 E‖ ≤ ε := by
  obtain ⟨K,hK⟩ := exists_hillGapFullEnergyProduct_inverse_free_bound
    q.val q.property.1 q.property.2 roots hroots
  obtain ⟨C,hC,hCb⟩ := exists_bound_exp_im_div_sin_of_separated
    (by positivity : 0 < Real.pi/4)
  let B : ℝ := ‖p‖ + ‖h‖
  let R : ℝ := max (4*B) (32*B^2*C/ε)
  obtain ⟨Kz,hKz⟩ := exists_nat_gt (R/Real.pi)
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop Kz] with k hk hkz
  intro E hE
  let z := Complex.sqrt E
  have hzmem := hillEnergyCircle_sqrt_mem_centralCircle k E hE
  have hnorm : ‖z‖ = centralCircleRadius k := by
    simpa only [mem_sphere,dist_zero_right] using hzmem
  have hzpos : 0 < ‖z‖ := by rw [hnorm]; exact centralCircleRadius_pos k
  have hz : z ≠ 0 := norm_pos_iff.mp hzpos
  have hR : R ≤ ‖z‖ := by
    have h1 : R < (Kz:ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp hKz
    have h2 : (Kz:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkz
    rw [hnorm]
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]
  have hsmall : 4*(‖p‖+‖h‖) ≤ ‖z‖ := (le_max_left _ _).trans hR
  have hsep := hillEnergyCircle_sqrt_free_separation k E hE
  have hsin : sin z ≠ 0 := sin_ne_zero_on_centralCircle k _ hzmem
  have hspos : 0 < ‖sin z‖ := norm_pos_iff.mpr hsin
  have hc : Real.exp |z.im| / ‖sin z‖ ≤ C := by
    simpa only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hCb z hsep
  have hN := hillL2Discriminant_mean_zero_variation_bound p h hzero z hz hsmall
  have hzsq : z^2 = E := complex_sqrt_sq E
  rw [hzsq] at hN
  let N : ℂ := (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant (Coeff.periodDouble a) E) p) h
  have hfree : sin z/z ≠ 0 := div_ne_zero hsin hz
  have hNb : ‖N/(sin z/z)‖ ≤ 16*B^2*C/‖z‖ := by
    rw [norm_div,norm_div,div_div_eq_mul_div]
    calc
      ‖N‖*‖z‖/‖sin z‖ ≤
          (16*Real.exp |z.im| *B^2/‖z‖^2)*‖z‖/‖sin z‖ := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hN (norm_nonneg z)) hspos.le
      _ = (16*B^2/‖z‖)*(Real.exp |z.im|/‖sin z‖) := by
        field_simp
      _ ≤ (16*B^2/‖z‖)*C := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  obtain ⟨hp,hpb⟩ := hK k hk E hE
  have he : N/hillAbelianNumeratorProduct roots 0 E =
      (N/(sin z/z))*((sin z/z)/hillAbelianNumeratorProduct roots 0 E) := by
    field_simp
  rw [he,norm_mul]
  apply (mul_le_mul hNb hpb (norm_nonneg _) (by positivity)).trans
  have hr : 32*B^2*C/ε ≤ ‖z‖ := (le_max_right _ _).trans hR
  have hh := (div_le_iff₀ hε).mp hr
  apply (show (16*B^2*C/‖z‖)*2 = 32*B^2*C/‖z‖ by ring).le.trans
  exact (div_le_iff₀ hzpos).mpr (by nlinarith)

end NLS.KdV
