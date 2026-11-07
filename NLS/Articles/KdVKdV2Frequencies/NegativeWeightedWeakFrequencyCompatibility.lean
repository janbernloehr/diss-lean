import NLS.Articles.KdVKdV2Frequencies.GlobalNegativeWeightedFrequencyActionCharts
import NLS.Articles.KdVKdV2Frequencies.NormalizedSobolevWeakActions
import NLS.SequenceSpaces.FiniteConeCalibration

/-! The intermediate packets agree with the same actual weak scalar
frequency on the entire cone. Finite physical calibration and continuity
remove all finite support assumptions from the final identity. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem negativeWeighted_packet_agrees_actual_weak_frequency
    (D : GlobalRoughAbelianForwardData) (β t : ℝ)
    (hβ : 0<β) (hβ1 : β<1) (ht : 0<t) (hβt : 2*t=1-β)
    (U : Set (Coeff 1)) (F : Coeff 1 → Coeff 1)
    (hU : IsOpen U) (hCU : Coeff.nonnegativeLocus 1⊆U) (hF : AnalyticOnNhd ℂ F U)
    (hpair : ∀ (P : NegativeWeightedFrequencyPairChart D β t) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → F (quadraticActionsExponent (q := 1) z)=P.packet z)
    (V : Set (Coeff 1)) (G : ℕ+ → Coeff 1 → ℂ)
    (hV : IsOpen V) (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n,
        G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a : Coeff 1) (ha : a∈Coeff.nonnegativeLocus 1) (n : ℕ+) :
    F a (n : ℤ)=(Weight.sobolev (-β) (n : ℤ) : ℂ)*
      G n (normalizedSobolevWeakActionInclusion (-β) (by linarith) a) := by
  let κ := normalizedSobolevWeakActionInclusion (-β) (by linarith : -1≤-β)
  let T := κ ⁻¹' V
  have hT : IsOpen T := hV.preimage κ.continuous
  have hCT : Coeff.nonnegativeLocus 1⊆T := fun b hb =>
    hCV (normalizedSobolevWeakActionInclusion_nonnegative (-β) (by linarith) b hb)
  have hf : ContinuousOn (fun b => F b (n : ℤ)) U := by
    intro b hb
    exact (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 (n : ℤ)).analyticAt _).comp
      (hF b hb)).continuousAt.continuousWithinAt
  have hg : ContinuousOn (fun b => (Weight.sobolev (-β) (n : ℤ) : ℂ)*G n (κ b)) T := by
    intro b hb
    exact (analyticAt_const.mul ((hG n _ hb).comp (κ.analyticAt b))).continuousAt.continuousWithinAt
  apply Coeff.eq_on_cone_of_finite_calibration U T hU hT hCU hCT _ _ hf hg _ a ha
  intro b hb S hS
  obtain ⟨z,hzr,hQ,hzS⟩ := Coeff.exists_finite_real_quadraticActions_lift b hb S hS
  obtain ⟨P,hzP⟩ := exists_negativeWeightedFrequencyPairChart D β t hβ hβ1 ht hβt z hzr
  obtain ⟨c,hc,hcf⟩ := P.finite_physical_recovery z hzP hzr S hzS
  have he : κ b=baseActionNormalization (baseActionInclusion (originalActionInclusion c.val)) := by
    ext k
    rw [normalizedSobolevWeakActionInclusion_apply]
    have hck := hc k
    rw [show 2*t-1=-β by linarith] at hck
    have hQk := congrArg (fun v : Coeff 1 => v k) hQ
    rw [←hQk,←hck,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
    rfl
  have hp : F b (n : ℤ)=(Weight.sobolev (-β) (n : ℤ) : ℂ)*P.correction n z := by
    rw [←hQ,hpair P z hzP hzr,P.positive z hzP n]
    rfl
  rw [hp,he,weak_scalar_original_physical_recovery D G hrec c n,hcf n]

end NLS.Articles.KdVKdV2Frequencies
