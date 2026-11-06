import NLS.KdV.HillHminusArbitraryBaseActionRatios
import NLS.KdV.HillHminusUniformActionAmplitude

/-! # Uniformly invertible high action amplitudes near any rough source

One complex neighborhood works before all sufficiently high indices.
The actual principal square roots recover the original physical Abelian
amplitudes at every physical source in that rough neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_arbitrary_base_high_physical_action_amplitudes
    (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ B : PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ B V ∧
        (∀ a ∈ V, 1/8 ≤ Real.sqrt (1+(n : ℝ))*‖B a‖ ∧
          Real.sqrt (1+(n : ℝ))*‖B a‖ ≤ 2) ∧
        ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ V →
          B (hillOriginalHminusSource p.val) =
            hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ :=
    exists_hillHminus_arbitrary_base_high_physical_action_ratios q
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨R,hRa,hRb,hRp⟩ := hfamily n hn
  refine ⟨hillHminusActionRatioAmplitude R,?_,?_,?_⟩
  · intro a ha
    have hslit : 2*R a ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      left
      simp only [mul_re,show (2 : ℂ).re=2 from rfl,show (2 : ℂ).im=0 from rfl,
        zero_mul,sub_zero]
      linarith [(hRb a ha).2.1]
    exact ((Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hslit)).comp
      (f := fun a => 2*R a) (analyticAt_const.mul (hRa a ha))).div_const
  · intro a ha
    have hnpos : (0 : ℝ) < n := by positivity
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.property
    have hsq := norm_sq_hillHminusActionRatioAmplitude R a
    constructor
    · let d : ℝ := 2*Real.pi*(n : ℝ)
      have hd : 0 < d := by dsimp only [d]; positivity
      have hp : (1/2 : ℝ) ≤ d*‖R a‖ := by
        have hh := norm_le_norm_sub_add (1 : ℂ) ((d : ℂ)*R a)
        rw [norm_one,norm_sub_rev,norm_mul,norm_real,Real.norm_of_nonneg hd.le] at hh
        have hnear := (hRb a ha).2.2
        rw [show (2*Real.pi*(n : ℝ) : ℂ) = (d : ℂ) from by
          dsimp only [d]; push_cast; ring] at hnear
        linarith
      have hd8 : d ≤ 8*(n : ℝ) := by
        dsimp only [d]
        nlinarith [mul_nonneg (show 0 ≤ 4-Real.pi by linarith [Real.pi_lt_four]) hnpos.le]
      have hx : (1/16 : ℝ) ≤ (n : ℝ)*‖R a‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hd8 (norm_nonneg (R a))]
      apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1/8) (by positivity)).mp
      rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1+(n : ℝ)),hsq]
      nlinarith [norm_nonneg (R a)]
    · have hb : (n : ℝ)*‖hillHminusActionRatioAmplitude R a‖^2 ≤ 2 := by
        rw [hsq]
        have hh := (le_div_iff₀ hnpos).mp (hRb a ha).1
        nlinarith
      apply (sq_le_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 2)).mp
      rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1+(n : ℝ))]
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg ‖hillHminusActionRatioAmplitude R a‖)]
  · intro p hp
    have hratio := hRp p hp
    have hreal := hillActionGapRatio_real_positive p.val p.property.1 p.property.2 (n : ℕ) n.property
    have hcast : hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) =
        ((hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ)).re : ℂ) := by
      apply Complex.ext <;> simp only [ofReal_re,ofReal_im,hreal.2]
    rw [hillHminusActionRatioAmplitude,hratio,hcast,← ofReal_ofNat,← ofReal_mul,
      Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hreal.1.le))]
    rfl

end NLS.KdV
