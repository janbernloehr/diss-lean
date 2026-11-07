import NLS.SequenceSpaces.FourierRealTorusNoncompact
import NLS.SequenceSpaces.FourierRealPhaseFlow
import Mathlib.Topology.Algebra.Order.Field

/-! Strong continuity of a physical infinity-endpoint phase orbit with
diverging frequencies forces the exact weighted c0 condition. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem positiveWeightedC0_of_continuous_phases (w : Weight)
    (a : fourierRealZeroSubmodule w ⊤) (f : ℝ → fourierRealZeroSubmodule w ⊤)
    (hf0 : f 0=a) (freq : ℕ → ℝ) (hfreq : Tendsto freq atTop atTop)
    (hcoef : ∀ t : ℝ, ∀ j : ℕ, (f t).val.val.val ((j+1:ℕ):ℤ)=
      Complex.exp (-((t*freq j:ℝ):ℂ)*Complex.I)*a.val.val.val ((j+1:ℕ):ℤ))
    (hc : ContinuousAt f 0) : PositiveWeightedC0 w a := by
  have htime : Tendsto (fun j => Real.pi/freq j) atTop (𝓝 (0:ℝ)) := hfreq.const_div_atTop Real.pi
  have hlim := hc.tendsto.comp htime
  rw [hf0] at hlim
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  obtain ⟨M,hM⟩ := (eventually_atTop.mp (hfreq.eventually (eventually_gt_atTop 0)))
  refine ⟨max N M+1,?_⟩
  intro n hn
  have hn1 : 1≤n := by omega
  let j := n-1
  have hj : j+1=n := by dsimp [j]; omega
  have hjN : N≤j := by dsimp [j]; omega
  have hjM : M≤j := by dsimp [j]; omega
  have hclose := hN j hjN
  have hp := hM j hjM
  let t := Real.pi/freq j
  have hco : (f t).val.val.val (n:ℤ)=-a.val.val.val (n:ℤ) := by
    rw [← hj,hcoef,show t*freq j=Real.pi from div_mul_cancel₀ _ hp.ne',neg_mul,
      Complex.exp_neg,Complex.exp_pi_mul_I]
    simp
  have hraw := norm_apply_le w ⊤ ((f t).val.val-a.val.val) (n:ℤ)
  have hd : 2*(w n*‖a.val.val.val n‖)≤dist (f t) a := by
    have hv := (le_div_iff₀ (w.positive (n:ℤ))).mp hraw
    rw [sub_val,hco] at hv
    have he : -a.val.val.val (n:ℤ)-a.val.val.val (n:ℤ)=(-2:ℂ)*a.val.val.val (n:ℤ) := by ring
    rw [he,norm_mul] at hv
    norm_num only [norm_neg,Complex.norm_ofNat] at hv
    rw [dist_eq_norm]
    change 2*(w n*‖a.val.val.val n‖)≤‖(f t).val.val-a.val.val‖
    nlinarith
  have hnonneg : 0≤w n*‖a.val.val.val n‖ := mul_nonneg (w.positive _).le (norm_nonneg _)
  change dist (f t) a<ε at hclose
  linarith

theorem positiveWeightedC0_of_continuous_positive_phases (w : Weight)
    (a : fourierRealZeroSubmodule w ⊤) (f : ℝ → fourierRealZeroSubmodule w ⊤)
    (hf0 : f 0=a) (freq : ℕ → ℝ) (hfreq : Tendsto freq atTop atTop)
    (hcoef : ∀ t : ℝ, ∀ j : ℕ, (f t).val.val.val ((j+1:ℕ):ℤ)=
      Complex.exp (((t*freq j:ℝ):ℂ)*Complex.I)*a.val.val.val ((j+1:ℕ):ℤ))
    (hc : ContinuousAt f 0) : PositiveWeightedC0 w a := by
  apply positiveWeightedC0_of_continuous_phases w a (fun t => f (-t)) (by simpa only [neg_zero] using hf0) freq hfreq
  · intro t j
    rw [hcoef]
    simp only [neg_mul,Complex.ofReal_neg]
  · have hn : Tendsto (fun t : ℝ => -t) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa only [neg_zero] using (continuous_neg.tendsto (0:ℝ))
    simpa only [ContinuousAt,Function.comp_def,neg_zero] using hc.tendsto.comp hn

end NLS.WeightedCoeff
