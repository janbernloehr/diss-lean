import NLS.KdV.HillL2LogDerivativeComparison
import NLS.KdV.HillRadiusMidpointMoments
import NLS.KdV.HillConstantGapMidpoint
import NLS.KdV.HillMiuraL2Discriminant
import NLS.ComplexAnalysis.CenteredCircleMomentComparison
import NLS.ComplexAnalysis.LogDerivativeLocal

/-! # A quadratic mean-subtracted bound for every actual complex gap midpoint -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillLocalGapMidpoint_all_quadratic_bound :
    ∃ η K : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧ ∀ u ∈ ball (0 : Coeff 2) η, ∀ k : ℕ+,
      ‖hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)-freeHillEnergy k-u 0‖ ≤
        K*‖u‖^2/(k : ℝ) := by
  obtain ⟨ηb,b,hηb,hb,hlower⟩ := exists_hillL2_all_annular_radicand_lower_bound
  obtain ⟨ηm,hηm,hmom⟩ := exists_hillFreeGap_all_radius_moment_identification h0q h0r
  obtain ⟨ηc,hηc,hconst⟩ := exists_hillFreeGap_all_constant_midpoint h0q h0r
  let η := min ηb (min ηm (min ηc (min 1 (1/(4*Real.exp 1)))))
  have hη : 0 < η := lt_min hηb (lt_min hηm (lt_min hηc (lt_min (by norm_num) (by positivity))))
  have hηb' : η ≤ ηb := min_le_left _ _
  have hηm' : η ≤ ηm := (min_le_right _ _).trans (min_le_left _ _)
  have hηc' : η ≤ ηc := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη1 : η ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηs : η ≤ 1/(4*Real.exp 1) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let A := 32*(Real.exp 1)^3*(4*Real.exp 1+16*(Real.exp 1)^2)
  let B := (2*Real.exp 1+8*(Real.exp 1)^2)^2+4
  let K := 4*A/b+4*B*A/b^2
  have hK : 0 < K := by dsimp only [K,A,B]; positivity
  refine ⟨η,K,hη,hη1,hK,?_⟩
  intro u hu k
  let v : Coeff 2 := lp.single 2 0 (u 0)
  have hv : ‖v‖ ≤ ‖u‖ := by
    rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    exact lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) u 0
  have hvball : v ∈ ball (0 : Coeff 2) η := mem_ball_zero_iff.mpr (hv.trans_lt (mem_ball_zero_iff.mp hu))
  have hmean : u 0 = v 0 := by simp only [v,lp.single_apply,Pi.single_eq_same]
  have hnu : ‖u‖ ≤ 1 := (mem_ball_zero_iff.mp hu).le.trans hη1
  have hs : 4*Real.exp 1*‖u‖ ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*Real.exp 1)).mp ((mem_ball_zero_iff.mp hu).le.trans hηs)
    nlinarith
  have hboundary (w : Coeff 2) (hw : w ∈ ball 0 η) (E : ℂ)
      (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) : b ≤ ‖hillL2Radicand (Coeff.periodDouble w) E‖ := by
    have hd := mem_sphere_iff_norm.mp hE
    exact hlower w (ball_subset_ball hηb' hw) k E (by rw [hd]; linarith [show (0 : ℝ) < k by positivity])
      (by rw [hd]; linarith [show (0 : ℝ) < k by positivity])
  have hnonzero (w : Coeff 2) (hw : w ∈ ball 0 η) (E : ℂ)
      (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) : hillL2Radicand (Coeff.periodDouble w) E ≠ 0 :=
    norm_pos_iff.mp (hb.trans_le (hboundary w hw E hE))
  have hmomw (w : Coeff 2) (hw : w ∈ ball 0 η) := hmom k (Coeff.periodDouble w)
    (by rw [mem_ball_zero_iff,Coeff.norm_periodDouble]; exact (mem_ball_zero_iff.mp hw).trans_le hηm')
    (hnonzero w hw)
  let f := logDeriv (hillL2Radicand (Coeff.periodDouble u))
  let g := logDeriv (hillL2Radicand (Coeff.periodDouble v))
  have hf : ContinuousOn f (sphere (freeHillEnergy k) (k : ℝ)) := by
    intro E hE
    exact (analyticAt_logDeriv (analyticOnNhd_hillL2Radicand _ E (mem_univ _))
      (hnonzero u hu E hE)).continuousAt.continuousWithinAt
  have hg : ContinuousOn g (sphere (freeHillEnergy k) (k : ℝ)) := by
    intro E hE
    exact (analyticAt_logDeriv (analyticOnNhd_hillL2Radicand _ E (mem_univ _))
      (hnonzero v hvball E hE)).continuousAt.continuousWithinAt
  have hzero : (2*Real.pi*I : ℂ)⁻¹*(∮ E in C(freeHillEnergy k,(k : ℝ)), f E) =
      (2*Real.pi*I : ℂ)⁻¹*(∮ E in C(freeHillEnergy k,(k : ℝ)), g E) := by
    have hmu := (hmomw u hu).1
    have hmv := (hmomw v hvball).1
    simp only [logarithmicCircleMoment,pow_zero,one_mul] at hmu hmv
    exact hmu.trans hmv.symm
  have hdiff (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) :
      ‖f E-g E‖ ≤ K*‖u‖^2/(k : ℝ)^3 :=
    hillL2Radicand_same_mean_logDeriv_bound u v hmean hv hnu hs k E hE b hb
      (hboundary u hu E hE) (hboundary v hvball E hE)
  have hmoment := norm_normalized_first_moment_sub_le f g (freeHillEnergy k)
    (by positivity : (0 : ℝ) ≤ k) hf hg hzero hdiff
  have hfirst (w : Coeff 2) (hw : w ∈ ball 0 η) := (hmomw w hw).2
  simp only [logarithmicCircleMoment,pow_one] at hfirst
  dsimp only [f,g] at hmoment
  rw [hfirst u hu,hfirst v hvball] at hmoment
  have hcv : hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble v) = freeHillEnergy k+u 0 := by
    rw [show Coeff.periodDouble v = lp.single 2 0 (u 0) from periodDouble_single_zero _]
    exact hconst _ ((lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) u 0).trans_lt
      ((mem_ball_zero_iff.mp hu).trans_le hηc')) k
  rw [hcv,show 2*hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)-2*(freeHillEnergy k+u 0) =
    2*(hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)-freeHillEnergy k-u 0) by ring,
    norm_mul,norm_ofNat] at hmoment
  have hk : (0 : ℝ) < k := by positivity
  have he : (k : ℝ)^2*(K*‖u‖^2/(k : ℝ)^3) = K*‖u‖^2/(k : ℝ) := by field_simp
  rw [he] at hmoment
  linarith [norm_nonneg (hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)-freeHillEnergy k-u 0)]

end NLS.KdV
