import NLS.KdV.HillHighNormalizedContourBound
import NLS.KdV.HillBaseContourPeriodComparison
import NLS.KdV.HillHighFreeContourBandBounds
import NLS.KdV.HillRegularCorrectionContourBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem norm_le_cubic_decay_of_scaled_freeHillValue_bound (n k : ℕ) (hn : 1 ≤ n)
    (hkn : 2*n ≤ k) (C : ℝ) (z : ℂ)
    (hbound : ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*z‖ ≤ C/(k : ℝ)) :
    ‖z‖ ≤ (2*(n : ℝ)*C/Real.pi^2)/(k : ℝ)^3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkn' : 2*(n : ℝ) ≤ k := by exact_mod_cast hkn
  have hdiff : freeHillValue k-freeHillValue n = Real.pi^2*((k : ℝ)^2-(n : ℝ)^2) := by
    simp only [freeHillValue,Int.cast_natCast]
    ring
  have hsquare : (k : ℝ)^2/2 ≤ (k : ℝ)^2-(n : ℝ)^2 := by nlinarith
  have hdiffpos : 0 < freeHillValue k-freeHillValue n := by
    rw [hdiff]
    exact mul_pos (sq_pos_of_pos Real.pi_pos) (by nlinarith)
  rw [norm_mul,norm_div,← ofReal_sub,norm_real,Real.norm_eq_abs,abs_of_pos hdiffpos,
    Complex.norm_natCast] at hbound
  have hsmall : (Real.pi^2/2*(k : ℝ)^2)/(n : ℝ) ≤ (freeHillValue k-freeHillValue n)/(n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hn0.le
    rw [hdiff]
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hmul := (mul_le_mul_of_nonneg_right hsmall (norm_nonneg z)).trans hbound
  rw [le_div_iff₀ (pow_pos hk0 3),div_eq_mul_inv] at ⊢
  have hm := (mul_le_mul_of_nonneg_right hmul (by positivity : 0 ≤ 2*(n : ℝ)*(k : ℝ)/Real.pi^2))
  convert hm using 1 <;> field_simp

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

include h0q h0r

theorem exists_hillRegularAbelianCorrection_quadratic_decay (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, N ≤ k → ∀ hk : 1 ≤ k,
      ‖hillRegularAbelianCorrection q hq hr n hn k hk‖ ≤ C/(k : ℝ)^2 := by
  obtain ⟨N,hN,C,hC,hscaled⟩ := exists_hillAbelianSelectedGlobalPsi_scaled_high_contour_bound h0q h0r q hq hr n hn
  let p := SpectralWeight.one.toCoeff q
  obtain ⟨M,hM,D,hD,hcontrol⟩ := exists_hillAbelianComplexPeriod_bounded_tail_control h0q h0r ‖p‖
  refine ⟨max (max N M) (2*n), hN.trans ((le_max_left N M).trans (le_max_left _ _)),
    4*Real.pi*(n : ℝ)*C, by positivity,?_⟩
  intro k hk hk1
  have hkN : N ≤ k := (le_max_left N M).trans ((le_max_left _ _).trans hk)
  have hkM : M ≤ k := (le_max_right N M).trans ((le_max_left _ _).trans hk)
  have hk2n : 2*n ≤ k := (le_max_right _ _).trans hk
  have hnk : n ≠ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let A := 2*(n : ℝ)*C/Real.pi^2
  have hA : 0 ≤ A := by positivity
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hRle : R ≤ Real.pi^2*(k : ℝ)/2 := by
    dsimp only [R]
    rw [hillFreeGapHalfLength h0q h0r k hk1,zero_add,hillFreeGapCollar h0q h0r k hk1]
    nlinarith [sq_nonneg Real.pi]
  have hband := hillHighFreeContour_physical_band_bounds_of_control h0q h0r M hM ‖p‖ D hcontrol q hq hr le_rfl k hkM
  have hfill : closedBall (hillRealGapCenter 0 h0q h0r k : ℂ) R ⊆ hillGapFilledDomain q hq hr k := by
    intro z hz
    have hre := re_bounds_of_mem_realCenteredClosedBall hz
    exact Or.inr ⟨by linarith [hband.1,hre.1],by linarith [hband.2,hre.2]⟩
  have hgap := hillRealGap_mem_high_free_contour_ball_of_control h0q h0r M hM ‖p‖ D hcontrol q hq hr le_rfl k hkM
  have h := norm_hillRegularAbelianCorrection_le_of_contour_bound q hq hr n k hn hk1 hnk.symm
    (hillRealGapCenter 0 h0q h0r k : ℂ) R (A/(k : ℝ)^3) hR (by positivity) hfill hgap
      (fun E hE => norm_le_cubic_decay_of_scaled_freeHillValue_bound n k hn hk2n C _ (hscaled k hkN hnk E hE))
  apply h.trans
  calc
    4*Real.pi*R*(A/(k : ℝ)^3) ≤ 4*Real.pi*(Real.pi^2*(k : ℝ)/2)*(A/(k : ℝ)^3) := by gcongr
    _ = (4*Real.pi*(n : ℝ)*C)/(k : ℝ)^2 := by dsimp only [A];field_simp

end NLS.KdV
