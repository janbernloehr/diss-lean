import NLS.KdV.HillNativeTraceNumerator
import NLS.KdV.HillAllSymmetricGapCharts
import NLS.ComplexAnalysis.QuadraticGapActionRatioBounds

/-! # Uniform complex analytic action-to-gap ratios for every positive gap -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeActionGapRatio (k : ℕ+) (u : Coeff 2) : ℂ :=
  quadraticGapActionRatio (hillNativeFilledTraceNumerator h0q h0r k)
    (fun v => hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble v))
    (fun v => hillLocalGapSquare 0 h0q h0r (k : ℕ) (Coeff.periodDouble v)/4) u

theorem exists_hillNativeActionGapRatio_all_analytic_bound :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ k : ℕ+,
      AnalyticOnNhd ℂ (hillNativeActionGapRatio h0q h0r k) (ball (0 : Coeff 2) η) ∧
      ∀ u ∈ ball (0 : Coeff 2) η, ‖hillNativeActionGapRatio h0q h0r k u‖ ≤ C/(k : ℝ) := by
  obtain ⟨ηt,C,hηt,hC,hT⟩ := exists_hillNativeFilledTraceNumerator_all_bound h0q h0r
  obtain ⟨ηs,hηs,_,hS⟩ := exists_hillLocalGap_all_symmetric_charts h0q h0r
  let η := min ηt ηs
  have hη : 0 < η := lt_min hηt hηs
  have ht : ball (0 : Coeff 2) η ⊆ ball 0 ηt := ball_subset_ball (min_le_left _ _)
  have hsource (u : Coeff 2) (hu : u ∈ ball 0 η) : Coeff.periodDouble u ∈ ball (0 : Coeff 2) ηs := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (mem_ball_zero_iff.mp hu).trans_le (min_le_right _ _)
  refine ⟨η,4*C,hη,by positivity,?_⟩
  intro k
  let T := hillNativeFilledTraceNumerator h0q h0r k
  let τ := fun u : Coeff 2 => hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)
  let s := fun u : Coeff 2 => hillLocalGapSquare 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)/4
  let d := fun u => sqrt (s u)
  let D := ball (freeHillEnergy k) (k : ℝ) ×ˢ ball (0 : Coeff 2) η
  have hD : IsOpen D := isOpen_ball.prod isOpen_ball
  have hTa : AnalyticOnNhd ℂ T D := (hT k).1.mono (fun t ht' => ⟨ball_subset_closedBall ht'.1,ht ht'.2⟩)
  have hTd := analyticOnNhd_spectral_deriv_of_analyticOnNhd T D hD hTa
  have hτ : AnalyticOnNhd ℂ τ (ball (0 : Coeff 2) η) := by
    intro u hu
    exact ((hS k).1 _ (hsource u hu)).comp (Coeff.periodDouble.toContinuousLinearMap.analyticAt u)
  have hs : AnalyticOnNhd ℂ s (ball (0 : Coeff 2) η) := by
    intro u hu
    exact (((hS k).2.1 _ (hsource u hu)).comp (Coeff.periodDouble.toContinuousLinearMap.analyticAt u)).div_const
  have hsmall (u : Coeff 2) (hu : u ∈ ball 0 η) : ‖τ u-freeHillEnergy k‖ ≤ (k : ℝ)/16 ∧
      ‖d u‖ ≤ (k : ℝ)/16 := (hS k).2.2 _ (hsource u hu)
  have hk : (0 : ℝ) < k := by positivity
  refine ⟨?_,?_⟩
  · intro u hu
    have hsq : AnalyticAt ℂ (fun v => (d v)^2) u := by
      simpa only [d,complex_sqrt_sq] using hs u hu
    have hm := analyticAt_parametricSineSquareCosineMean_of_analytic_square
      (fun t : ℂ × Coeff 2 => deriv (fun E => T (E,t.2)) t.1) τ d D hD hTd u
      (hτ u hu) hsq ((k : ℝ)/4) (by linarith [(hsmall u hu).2]) (by
        intro E hE
        refine ⟨?_,hu⟩
        rw [mem_ball_iff_norm]
        have hnorm := norm_sub_le_norm_sub_add_norm_sub E (τ u) (freeHillEnergy k)
        have hh := mem_closedBall_iff_norm.mp hE
        linarith [(hsmall u hu).1])
    exact analyticAt_const.mul hm
  · intro u hu
    have hpoint (θ : ℝ) (_ : θ ∈ Icc (0 : ℝ) Real.pi) :
        ‖deriv (fun E => T (E,u)) (τ u+d u*(Real.cos θ : ℂ))‖ ≤ 2*C/(k : ℝ) := by
      apply (hT k).2 u (ht hu) |>.2
      rw [mem_closedBall_iff_norm]
      have hc : ‖(Real.cos θ : ℂ)‖ ≤ 1 := by
        simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
      have hm := mul_le_mul_of_nonneg_left hc (norm_nonneg (d u))
      have he := norm_add_le (τ u-freeHillEnergy k) (d u*(Real.cos θ : ℂ))
      rw [show τ u-freeHillEnergy k+d u*(Real.cos θ : ℂ)=τ u+d u*(Real.cos θ : ℂ)-freeHillEnergy k by ring,
        norm_mul] at he
      nlinarith [(hsmall u hu).1,(hsmall u hu).2]
    have h := norm_quadraticGapActionRatio_le T τ s u (by positivity : 0 ≤ 2*C/(k : ℝ)) hpoint
    apply h.trans_eq
    ring

end NLS.KdV
