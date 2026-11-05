import NLS.KdV.HillHminusLocalFilledTrace
import NLS.KdV.HillActionGapRatioRoughContinuation
import NLS.KdV.HillNativeAmplitudePrefactor

/-! # Actual physical action-to-gap amplitude germs in the rough norm

The Cauchy construction uses the actual entire rough characteristic and
retains the original L2 formulas on every complex L2 inclusion. Analytic
continuation along real source lines gives physical matching throughout
each rough ball, without any smallness condition on the physical L2 norm.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillHminusLocalActionGapRatio (n : ℕ+) : PeriodOneHminusOne → ℂ :=
  quadraticGapActionRatio (hillHminusLocalDeflatedTrace h0q h0r n)
    (hillHminusLocalGapMidpoint h0q h0r n) (fun q => hillHminusLocalGapSquare h0q h0r n q/4)

def hillHminusLocalActionAmplitude (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  sqrt (2*hillHminusLocalActionGapRatio h0q h0r n q)/(Real.sqrt 2 : ℂ)

theorem hillHminusLocalActionGapRatio_l2 (n : ℕ+) (u : Coeff 2) :
    hillHminusLocalActionGapRatio h0q h0r n (periodOneL2Inclusion u) =
      hillLocalActionGapRatio 0 h0q h0r (n : ℕ) (Coeff.periodDouble u) := by
  simp only [hillHminusLocalActionGapRatio,hillLocalActionGapRatio,quadraticGapActionRatio,
    parametricSineSquareCosineMean,hillHminusLocalGapMidpoint_l2,
    hillHminusLocalGapSquare_l2,hillHminusLocalDeflatedTrace_l2]

theorem analyticAt_hillHminusLocalActionGapRatio_zero (n : ℕ+) :
    AnalyticAt ℂ (hillHminusLocalActionGapRatio h0q h0r n) 0 := by
  obtain ⟨V,_,h0V,hM,hS⟩ := exists_hillHminusLocalGapMoments_analytic h0q h0r n
  apply analyticAt_quadraticGapActionRatio_of_collapse
  · simpa only [(hillHminusLocalGapMoments_zero h0q h0r n).1] using
      analyticAt_hillHminusLocalDeflatedTrace_zero h0q h0r n
  · exact hM 0 h0V
  · exact (hS 0 h0V).div_const
  · rw [(hillHminusLocalGapMoments_zero h0q h0r n).2,zero_div]

theorem hillHminusLocalActionGapRatio_eventually_eq_physical (n : ℕ+) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      hillHminusLocalActionGapRatio h0q h0r n (hillPhysicalHminusEmbedding p).val =
        hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) := by
  filter_upwards [hillLocalActionGapRatio_eventually_eq_physical 0 h0q h0r (n : ℕ) n.property]
    with p hp
  have he := hillHminusLocalActionGapRatio_l2 h0q h0r n
    (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))
  rw [hillPeriodDouble_unitSample _ p.property.1] at he
  exact he.trans hp

theorem hillHminusLocalActionGapRatio_zero (n : ℕ+) :
    hillHminusLocalActionGapRatio h0q h0r n 0 = (2*(n : ℂ)*Real.pi)⁻¹ := by
  have h := (hillHminusLocalActionGapRatio_eventually_eq_physical h0q h0r n).self_of_nhds
  have he : (hillPhysicalHminusEmbedding (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)).val = 0 := by
    simp only [hillPhysicalHminusEmbedding,map_zero]
  rw [he,hillActionGapRatio_free h0q h0r (n : ℕ) n.property] at h
  exact h

theorem exists_hillHminusLocalActionGapRatio_analytic_positive_physical (n : ℕ+) :
    ∃ η : ℝ, 0 < η ∧ AnalyticOnNhd ℂ (hillHminusLocalActionGapRatio h0q h0r n)
      (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) η, 0 < (hillHminusLocalActionGapRatio h0q h0r n q).re) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η →
        hillHminusLocalActionGapRatio h0q h0r n (hillPhysicalHminusEmbedding p).val =
          hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) := by
  have ha := analyticAt_hillHminusLocalActionGapRatio_zero h0q h0r n
  have hpos : 0 < (hillHminusLocalActionGapRatio h0q h0r n 0).re := by
    rw [hillHminusLocalActionGapRatio_zero]
    have he : (2*(n : ℂ)*Real.pi)⁻¹ = (((2*(n : ℝ)*Real.pi)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [he,ofReal_re]
    positivity
  have hc : ContinuousAt (fun q => (hillHminusLocalActionGapRatio h0q h0r n q).re) 0 :=
    Complex.continuous_re.continuousAt.comp ha.continuousAt
  have he := hc.tendsto.eventually (lt_mem_nhds hpos)
  obtain ⟨s,hs,hsub⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨r,hr,han⟩ := ha.exists_ball_analyticOnNhd
  let η := min r s
  have hη : 0 < η := lt_min hr hs
  have hηa := han.mono (ball_subset_ball (min_le_left r s))
  exact ⟨η,hη,hηa,(fun q hq => hsub (ball_subset_ball (min_le_right r s) hq)),
    fun p hp => hillActionGapRatio_eq_on_rough_ball_of_germ η hη (n : ℕ) n.property
      (hillHminusLocalActionGapRatio h0q h0r n) hηa h0q h0r
      (hillHminusLocalActionGapRatio_eventually_eq_physical h0q h0r n) p hp⟩

theorem exists_hillHminusLocalActionAmplitude_analytic_physical (n : ℕ+) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      AnalyticOnNhd ℂ (hillHminusLocalActionAmplitude h0q h0r n) (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) η,
        Real.sqrt (1+(n : ℝ))*‖hillHminusLocalActionAmplitude h0q h0r n q‖ ≤ C) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η →
        hillHminusLocalActionAmplitude h0q h0r n (hillPhysicalHminusEmbedding p).val =
          hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  obtain ⟨r,hr,hRa,hRpos,hphysical⟩ :=
    exists_hillHminusLocalActionGapRatio_analytic_positive_physical h0q h0r n
  have hBa : AnalyticOnNhd ℂ (hillHminusLocalActionAmplitude h0q h0r n) (ball 0 r) := by
    intro q hq
    have hslit : 2*hillHminusLocalActionGapRatio h0q h0r n q ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      left
      have hp := hRpos q hq
      simpa only [mul_re,show (2 : ℂ).re = 2 from rfl,show (2 : ℂ).im = 0 from rfl,
        zero_mul,sub_zero] using mul_pos (by norm_num : (0 : ℝ) < 2) hp
    exact ((Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hslit)).comp
      (f := fun q => 2*hillHminusLocalActionGapRatio h0q h0r n q)
      (analyticAt_const.mul (hRa q hq))).div_const
  have hc := (hBa 0 (mem_ball_self hr)).continuousAt
  have he := hc.preimage_mem_nhds (ball_mem_nhds (hillHminusLocalActionAmplitude h0q h0r n 0) zero_lt_one)
  obtain ⟨s,hs,hsub⟩ := Metric.mem_nhds_iff.mp he
  let η := min r s
  let C := Real.sqrt (1+(n : ℝ))*(‖hillHminusLocalActionAmplitude h0q h0r n 0‖+1)
  refine ⟨η,C,lt_min hr hs,by dsimp only [C]; positivity,
    hBa.mono (ball_subset_ball (min_le_left r s)),?_,?_⟩
  · intro q hq
    have hh := mem_ball_iff_norm.mp (hsub (ball_subset_ball (min_le_right r s) hq))
    have hb := norm_le_norm_sub_add (hillHminusLocalActionAmplitude h0q h0r n q)
      (hillHminusLocalActionAmplitude h0q h0r n 0)
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
  · intro p hp
    have hratio := hphysical p (ball_subset_ball (min_le_left r s) hp)
    have hR := hillActionGapRatio_real_positive p.val p.property.1 p.property.2 (n : ℕ) n.property
    have hcast : hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) =
        ((hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ)).re : ℂ) := by
      apply Complex.ext <;> simp only [ofReal_re,ofReal_im,hR.2]
    rw [hillHminusLocalActionAmplitude,hratio,hcast,← ofReal_ofNat,← ofReal_mul,
      Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR.1.le))]
    rfl

theorem hillHminusLocalActionAmplitude_zero (n : ℕ+) :
    hillHminusLocalActionAmplitude h0q h0r n 0 =
      (Real.sqrt (2*(n : ℝ)*Real.pi) : ℂ)⁻¹ := by
  obtain ⟨η,_,hη,_,_,_,hphysical⟩ :=
    exists_hillHminusLocalActionAmplitude_analytic_physical h0q h0r n
  let p : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  have hp : (hillPhysicalHminusEmbedding p).val = 0 := by
    simp only [p,hillPhysicalHminusEmbedding,map_zero]
  have he := hphysical p (by rw [hp]; exact mem_ball_self hη)
  rw [hp] at he
  exact he.trans (hillAbelianAmplitudePrefactor_free h0q h0r (n : ℕ) n.property)

end NLS.KdV
