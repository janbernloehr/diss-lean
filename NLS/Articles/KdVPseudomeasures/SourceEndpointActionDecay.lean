import NLS.Articles.KdVPseudomeasures.NativeEndpointBallBound
import NLS.Articles.KdVPseudomeasures.SourceEndpointGapSquareBound

/-! Uniform decay of the original canonical actions on full physical
endpoint norm balls, retaining the actual signed Birkhoff products. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem source_uniform_endpoint_action_power_bound (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : Potential r, ‖q.val‖ ≤ R → ∀ n : ℕ+,
      ‖originalCanonicalHillAction n (sourceOriginalPotential r hr q)‖ ≤ B^2/(n:ℝ)^(1-2*r) := by
  obtain ⟨B,hB,hbound⟩ := sourceLemma3_6 r hr R
  refine ⟨B,hB,?_⟩
  intro q hq n
  let z := originalEndpointRealSignedCoordinates r hr q
  have hz : ‖z.val.val‖≤B := hbound q hq
  have hn1 : (1:ℝ)≤n := by exact_mod_cast n.property
  have hw : Weight.signedSobolev (1/2-r) (n:ℤ)=(n:ℝ)^(1/2-r) := by
    change (max 1 |(n:ℝ)|)^(1/2-r)=_
    rw [abs_of_nonneg (by positivity),max_eq_right hn1]
  have hplus : ‖z.val.val.val (n:ℤ)‖≤B/(n:ℝ)^(1/2-r) := by
    have h := WeightedCoeff.norm_apply_le _ ⊤ z.val.val (n:ℤ)
    rw [hw] at h
    exact h.trans (div_le_div_of_nonneg_right hz (Real.rpow_nonneg (by positivity) _))
  have hminus : ‖z.val.val.val (-(n:ℤ))‖≤B/(n:ℝ)^(1/2-r) := by
    have h := WeightedCoeff.norm_apply_le _ ⊤ z.val.val (-(n:ℤ))
    rw [Weight.signedSobolev_neg,hw] at h
    exact h.trans (div_le_div_of_nonneg_right hz (Real.rpow_nonneg (by positivity) _))
  have he : originalCanonicalHillAction n (sourceOriginalPotential r hr q)=
      z.val.val.val (n:ℤ)*z.val.val.val (-(n:ℤ)) := by
    rw [originalCanonicalHillAction,originalPeriodOneCoefficients_sourceOriginalPotential]
    exact (original_endpoint_real_action r hr q n).symm
  rw [he,norm_mul]
  have hprod := mul_le_mul hplus hminus (norm_nonneg _) (by positivity : (0:ℝ)≤B/(n:ℝ)^(1/2-r))
  have hpow : ((n:ℝ)^(1/2-r))^2=(n:ℝ)^(1-2*r) := by
    rw [← Real.rpow_two,← Real.rpow_mul (by positivity : (0:ℝ)≤n)]
    congr 1
    ring
  exact hprod.trans_eq (by rw [← pow_two,div_pow,hpow])

theorem source_uniform_endpoint_action_decay (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ q : Potential r, ‖q.val‖≤R → ∀ n : ℕ+, N≤(n:ℕ) →
      ‖originalCanonicalHillAction n (sourceOriginalPotential r hr q)‖<ε := by
  obtain ⟨B,_,hB⟩ := source_uniform_endpoint_action_power_bound r hr R
  have hpow := (tendsto_rpow_neg_atTop (show (0:ℝ)<1-2*r by have hh:=hr.2; linarith)).comp
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun j : ℕ => B^2*(j:ℝ)^(-(1-2*r))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using hpow.const_mul (B^2)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨N,?_⟩
  intro q hq n hn
  apply (hB q hq n).trans_lt
  rw [div_eq_mul_inv,← Real.rpow_neg (by positivity : (0:ℝ)≤n)]
  exact hN (n:ℕ) hn

end NLS.Articles.KdVPseudomeasures
