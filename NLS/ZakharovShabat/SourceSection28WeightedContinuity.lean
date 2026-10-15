import NLS.ZakharovShabat.SourceSection28Asymptotics
import NLS.ZakharovShabat.SourceM1ActionContinuity

/-! # Continuity of the original complex weighted action sum

A locally bounded ℓ¹ realization has analytic scalar coordinates. Its norm
is the literal weighted absolute action sum, proving continuity throughout
the complex weighted part of the retained original and strip domains.
-/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Continuity on every complex weighted source whose decoded point lies in the original and strip domains. -/
theorem SourceSection11OriginalEstimates.section28_weighted_summable_continuousAt
    {W : Set (CoeffPair 2)} (H : SourceSection11OriginalEstimates (by simp) (by norm_num) W)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : CoeffPair 2)
    (haW : normalizedWeightedSource w a ∈ W)
    (haStrip : normalizedWeightedSource w a ∈ sourceSpectralStripNeighborhood (by simp)) :
    Summable (fun n : ℤ => (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ∧
    ContinuousAt (fun b : CoeffPair 2 => ∑' n : ℤ, (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w b)‖) a := by
  classical
  obtain ⟨U,hU,haU,hUW,M,hM,hbound⟩ := H.section28_locally_uniform _ haW
  let K := M+1
  have hK : 0 ≤ K := by dsimp [K]; linarith
  have hgap (b : CoeffPair 2) (hb : normalizedWeightedSource w b ∈ U) (n : ℤ) :
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w b)‖ ≤
        K*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (normalizedWeightedSource w b) n‖^2 := by
    obtain ⟨e,he,hen⟩ := hbound _ hb
    have hd := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) e n).trans hen
    rw [he n] at hd
    have ht := norm_add_le (4*sourceNormalizedIndexedAction (by simp) (by norm_num) n
      (normalizedWeightedSource w b)-1) (1:ℂ)
    rw [sub_add_cancel,norm_mul,Complex.norm_ofNat,norm_one] at ht
    have hn : ‖sourceNormalizedIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w b)‖ ≤ K := by
      dsimp [K]
      linarith [norm_nonneg (sourceNormalizedIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w b))]
    rw [H.previous.factorization _ (hUW hb) n,norm_mul,norm_pow,sourcePeriodicGapDisplacement_apply]
    nlinarith [mul_le_mul_of_nonneg_right hn (sq_nonneg
      ‖canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (normalizedWeightedSource w b))
        (periodOnePotential_mem (normalizedWeightedSource w b)) n‖)]
  let c : CoeffPair 2 → ℤ → ℂ := fun b n =>
    (w (2*n):ℂ)^2*sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w b)
  have hc (b : CoeffPair 2) (n : ℤ) : ‖c b n‖ = (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w b)‖ := by
    simp only [c,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  let bnd : CoeffPair 2 → ℝ := fun b => K*(265*Real.pi^2*(w.realExtension (16*‖b‖^2))^2*(1+‖b‖^2)*‖b‖^2)
  have hcont : Continuous bnd := by
    have he : Continuous (fun b : CoeffPair 2 => w.realExtension (16*‖b‖^2)) :=
      w.continuous_realExtension.comp (continuous_const.mul (continuous_norm.pow 2))
    exact continuous_const.mul (((continuous_const.mul (he.pow 2)).mul
      (continuous_const.add (continuous_norm.pow 2))).mul (continuous_norm.pow 2))
  let V := normalizedWeightedSource w ⁻¹' (U ∩ sourceSpectralStripNeighborhood (by simp)) ∩
    {b | bnd b < bnd a+1}
  have hV : IsOpen V := ((hU.inter (isOpen_sourceSpectralStripNeighborhood (by simp))).preimage
    (continuous_normalizedWeightedSource w)).inter (isOpen_lt hcont continuous_const)
  have haV : a ∈ V := ⟨⟨haU,haStrip⟩,by simp⟩
  have hdata (b : CoeffPair 2) (hb : b ∈ V) : Summable (fun n => ‖c b n‖) ∧ (∑' n, ‖c b n‖) ≤ bnd b := by
    obtain ⟨hgs,hgb⟩ := M1_source_canonicalGap_global_summable_and_le
      (normalizedWeightedSource w b) hb.1.2 w hw (normalizedWeightedPeriodOne w b)
      (weightedBaseToPair_normalizedWeightedPeriodOne w b)
    simp only [norm_normalizedWeightedPeriodOne] at hgb
    have hm (n : ℤ) : ‖c b n‖ ≤ K*(w (2*n)*
        ‖canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (normalizedWeightedSource w b))
          (periodOnePotential_mem (normalizedWeightedSource w b)) n‖)^2 := by
      rw [hc]
      have hh := mul_le_mul_of_nonneg_left (hgap b hb.1.1 n) (sq_nonneg (w (2*n)))
      rw [sourcePeriodicGapDisplacement_apply] at hh
      nlinarith [hh]
    have hs := (hgs.mul_left K).of_nonneg_of_le (fun n => norm_nonneg _) hm
    refine ⟨hs,?_⟩
    calc
      _ ≤ ∑' n, K*(w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num)
          (periodOnePotential (normalizedWeightedSource w b)) (periodOnePotential_mem (normalizedWeightedSource w b)) n‖)^2 :=
        hs.tsum_le_tsum hm (hgs.mul_left K)
      _ ≤ bnd b := by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hgb hK
  let F : CoeffPair 2 → Coeff 1 := fun b => if hb : b ∈ V then
    ⟨c b,by
      change Memℓp (c b) 1
      rw [memℓp_gen_iff (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
      simpa only [ENNReal.toReal_one,Real.rpow_one] using (hdata b hb).1⟩ else 0
  have hv (b : CoeffPair 2) (hb : b ∈ V) (n : ℤ) : F b n = c b n := by simp only [F,dif_pos hb]
  have hn (b : CoeffPair 2) (hb : b ∈ V) : ‖F b‖ = ∑' n, ‖c b n‖ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
    simp only [ENNReal.toReal_one,Real.rpow_one,one_div_one,hv b hb]
  have hF : ContinuousOn F V := by
    apply Coeff.continuousOn_of_bounded_coordinatewise (by simp) F hV _ (bnd a+1)
      (fun b hb => by rw [hn b hb]; exact (hdata b hb).2.trans hb.2.le)
    intro n b hb
    have hd : DifferentiableAt ℂ (fun d => c d n) b :=
      (((H.previous.previous.previous.previous.analytic n _ (hUW hb.1.1)).differentiableAt).comp b
        (normalizedWeightedSourceCLM w).differentiableAt).const_mul _
    have he : (fun d => c d n) =ᶠ[𝓝 b] (fun d => F d n) := by
      filter_upwards [hV.mem_nhds hb] with d hd
      exact (hv d hd n).symm
    exact (hd.congr_of_eventuallyEq he.symm).differentiableWithinAt
  refine ⟨(hdata a haV).1.congr (hc a),?_⟩
  apply ((hF a haV).continuousAt (hV.mem_nhds haV)).norm.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds haV] with b hb
  rw [hn b hb]
  simp only [hc]

/-- Continuity of the convergent original weighted action sum at every admissible complex source. -/
theorem SourceSection11OriginalEstimates.section28_weighted_continuousAt
    {W : Set (CoeffPair 2)} (H : SourceSection11OriginalEstimates (by simp) (by norm_num) W)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : CoeffPair 2)
    (haW : normalizedWeightedSource w a ∈ W)
    (haStrip : normalizedWeightedSource w a ∈ sourceSpectralStripNeighborhood (by simp)) :
    ContinuousAt (fun b : CoeffPair 2 => ∑' n : ℤ, (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w b)‖) a :=
  (H.section28_weighted_summable_continuousAt w hw a haW haStrip).2

end NLS.ZakharovShabat
