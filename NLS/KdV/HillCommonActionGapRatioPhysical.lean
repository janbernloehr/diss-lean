import NLS.KdV.HillCommonComplexActionGapRatio
import NLS.KdV.HillUniformRealGapLocalization
import NLS.KdV.HillActionGapFactor

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat MeasureTheory
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillComplexActionGapRatio_bounded_real_physical_matching (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖≤B →
        ∀ k : ℕ, N≤k → hillComplexActionGapRatio h0q h0r k (SpectralWeight.one.toCoeff q)=
          hillActionGapRatio q hq hr k := by
  obtain ⟨Ns,hNs,hs⟩ := exists_hillFreeGap_bounded_real_symmetric_data_matching h0q h0r B
  obtain ⟨Nh,hNh,hh⟩ := exists_hillComplexDeflatedTraceNumerator_bounded_real_physical_matching h0q h0r B
  obtain ⟨Nl,hNl,hl⟩ := exists_hillFreeGap_bounded_real_midpoint_halfgap_localization h0q h0r (1/16) (by norm_num) (by norm_num) B
  refine ⟨Ns+Nh+Nl,hNs.trans (by omega),?_⟩
  intro q hq hr hp k hk
  have hks : Ns≤k := by omega
  have hkh : Nh≤k := by omega
  have hkl : Nl≤k := by omega
  have hk1 := hNs.trans hks
  let p := SpectralWeight.one.toCoeff q
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let τ : ℂ := hillRealGapCenter q hq hr k
  let δ : ℂ := hillRealGapHalfLength q hq hr k
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  obtain ⟨hM,hS⟩ := hs q hq hr hp k hks
  obtain ⟨hτ,hδ⟩ := hl q hq hr hp k hkl
  have hsq : sqrt (hillLocalGapSquare 0 h0q h0r k p/4)^2=δ^2 := by
    rw [complex_sqrt_sq,hS]
    change (2*δ)^2/4=δ^2
    ring
  have hroot : parametricSineSquareCosineMean
      (fun x : ℂ × Coeff 2 => deriv (fun w => hillComplexDeflatedTraceNumerator h0q h0r k (w,x.2)) x.1)
      (hillLocalGapMidpoint 0 h0q h0r k) (sqrt (hillLocalGapSquare 0 h0q h0r k p/4),p)=
    parametricSineSquareCosineMean
      (fun x : ℂ × Coeff 2 => deriv (fun w => hillComplexDeflatedTraceNumerator h0q h0r k (w,x.2)) x.1)
      (hillLocalGapMidpoint 0 h0q h0r k) (δ,p) := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with he | he
    · rw [he]
    · rw [he,parametricSineSquareCosineMean_neg]
  have hz (θ : ℝ) : τ+δ*(Real.cos θ:ℂ)∈ball c R := by
    have hcos : ‖(Real.cos θ:ℂ)‖≤1 := by simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    rw [mem_ball,dist_eq_norm,show τ+δ*(Real.cos θ:ℂ)-c=(τ-c)+δ*(Real.cos θ:ℂ) by ring]
    have htri := norm_add_le (τ-c) (δ*(Real.cos θ:ℂ))
    have hmul := mul_le_mul_of_nonneg_left hcos (norm_nonneg δ)
    rw [norm_mul] at htri
    dsimp only [τ,δ,c,R] at *
    linarith
  dsimp only [hillComplexActionGapRatio,quadraticGapActionRatio]
  rw [hroot]
  congr 1
  unfold parametricSineSquareCosineMean
  rw [hM]
  apply intervalIntegral.integral_congr
  intro θ _
  have he : (fun w : ℂ => hillComplexDeflatedTraceNumerator h0q h0r k (w,p)) =ᶠ[𝓝 (τ+δ*(Real.cos θ:ℂ))]
      hillDeflatedTraceNumerator q hq hr k := by
    filter_upwards [isOpen_ball.mem_nhds (hz θ)] with w hw
    exact hh q hq hr hp k hkh w (ball_subset_closedBall hw)
  exact congrArg (fun v : ℂ => (Real.sin θ:ℂ)^2*v) he.deriv_eq

end NLS.KdV
