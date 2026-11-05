import NLS.KdV.HillUniformContourBound
import NLS.KdV.HillHighRegularCorrectionDecay
import NLS.KdV.HillBaseContourPeriodComparison
import NLS.KdV.HillHighFreeContourBandBounds
import NLS.KdV.HillRegularCorrectionContourBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

include h0q h0r

theorem exists_hillRegularAbelianCorrection_locally_uniform_quadratic_decay (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        ∀ k : ℕ, N ≤ k → ∀ hk : 1 ≤ k,
          ‖hillRegularAbelianCorrection r.val r.property.1 r.property.2 n hn k hk‖ ≤ C/(k : ℝ)^2 := by
  obtain ⟨N,hN,C,hC,hscaled⟩ := exists_hillSelectedPsi_locally_uniform_scaled_contour_bound h0q h0r q hq hr n hn
  let Q : RealPeriodOneHillPotential → Coeff 2 := fun r => SpectralWeight.one.toCoeff r.val
  have hQ : Continuous Q := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let B : ℝ := ‖SpectralWeight.one.toCoeff q‖+1
  have hpB : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential), ‖Q r‖ < B :=
    hQ.continuousAt.norm.eventually (isOpen_Iio.mem_nhds (show ‖Q ⟨q,hq,hr⟩‖ < B by dsimp [Q,B];linarith))
  obtain ⟨M,hM,D,hD,hcontrol⟩ := exists_hillAbelianComplexPeriod_bounded_tail_control h0q h0r B
  refine ⟨max (max N M) (2*n), hN.trans ((le_max_left N M).trans (le_max_left _ _)),
    4*Real.pi*(n : ℝ)*C, by positivity,?_⟩
  filter_upwards [hscaled,hpB] with r hrscaled hrB
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
  have hband := hillHighFreeContour_physical_band_bounds_of_control h0q h0r M hM B D hcontrol r.val r.property.1 r.property.2 hrB.le k hkM
  have hfill : closedBall (hillRealGapCenter 0 h0q h0r k : ℂ) R ⊆ hillGapFilledDomain r.val r.property.1 r.property.2 k := by
    intro z hz
    have hre := re_bounds_of_mem_realCenteredClosedBall hz
    exact Or.inr ⟨by linarith [hband.1,hre.1],by linarith [hband.2,hre.2]⟩
  have hgap := hillRealGap_mem_high_free_contour_ball_of_control h0q h0r M hM B D hcontrol r.val r.property.1 r.property.2 hrB.le k hkM
  have h := norm_hillRegularAbelianCorrection_le_of_contour_bound r.val r.property.1 r.property.2 n k hn hk1 hnk.symm
    (hillRealGapCenter 0 h0q h0r k : ℂ) R (A/(k : ℝ)^3) hR (by positivity) hfill hgap
      (fun E hE => norm_le_cubic_decay_of_scaled_freeHillValue_bound n k hn hk2n C _ (hrscaled k hkN hnk E hE))
  apply h.trans
  calc
    4*Real.pi*R*(A/(k : ℝ)^3) ≤ 4*Real.pi*(Real.pi^2*(k : ℝ)/2)*(A/(k : ℝ)^3) := by gcongr
    _ = (4*Real.pi*(n : ℝ)*C)/(k : ℝ)^2 := by dsimp only [A];field_simp

end NLS.KdV
