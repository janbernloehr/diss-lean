import NLS.ZakharovShabat.SourceM1ComplexActionBudget
import NLS.ZakharovShabat.SourceActionGapCorrection
import NLS.ZakharovShabat.NormalizedWeightedSourceTopology
import NLS.SequenceSpaces.SpectralWeightContinuity
import NLS.SequenceSpaces.BoundedCoordinateHolomorphic

/-! # Local ℓ¹ continuity of the actual complex weighted actions -/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A common complex neighborhood has analytic actions and a uniform gap-square bound. -/
theorem exists_local_sourceAction_gap_bound (ψ : CoeffPair 2)
    (hψ : IsRealType (CoeffPair.toMax 2 ψ)) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ ψ ∈ U ∧ ∃ K : ℝ, 0 ≤ K ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (sourceComplexAction (by simp) (by norm_num) n) U) ∧
      ∀ χ ∈ U, ∀ n : ℤ, ‖sourceComplexAction (by simp) (by norm_num) n χ‖ ≤
        K*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) χ n‖^2 := by
  obtain ⟨B,hB,hψB,M,hbound⟩ := exists_local_sourceNormalizedActionDeviation_coeff_uniformNorm
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num) (by norm_num : (1:ℝ≥0∞) < 2)
    (by simp) (by norm_num) ψ hψ
  obtain ⟨F,hF,hψF,_,hfactor⟩ := exists_local_sourceNormalizedAction_allIndices_analytic_factor
    (by simp) (by norm_num) ψ hψ
  obtain ⟨A,hA,hψA,hact,_⟩ := exists_local_sourceActionGapCorrection (by simp) (by norm_num) ψ hψ
  have hM : 0 ≤ M := by
    obtain ⟨b,_,hb⟩ := hbound ψ hψB
    exact (norm_nonneg b).trans hb
  let U := (B ∩ F) ∩ A
  refine ⟨U,(hB.inter hF).inter hA,⟨⟨hψB,hψF⟩,hψA⟩,M+1,by positivity,
    fun n χ hχ => hact n χ hχ.2,?_⟩
  intro χ hχ n
  apply sourceComplexAction_le_gap_sq_of_normalized_bound χ (M+1) (hfactor χ hχ.1.2) _ n
  intro k
  obtain ⟨b,hb,hbn⟩ := hbound χ hχ.1.1
  have hd := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) b k).trans hbn
  rw [hb k] at hd
  change ‖4*sourceNormalizedActionComplexExtension (by simp) (by norm_num) k χ-1‖ ≤ M at hd
  have he := norm_add_le (4*sourceNormalizedActionComplexExtension (by simp) (by norm_num) k χ-1) (1:ℂ)
  simp only [sub_add_cancel,norm_mul,norm_one] at he
  norm_num at he
  nlinarith [norm_nonneg (sourceNormalizedActionComplexExtension (by simp) (by norm_num) k χ)]

/-- The scale in the exact source estimate is continuous, also at zero. -/
def sourceM1ActionScale (w : SpectralWeight) (a : CoeffPair 2) : ℝ :=
  (w.realExtension (16*‖a‖^2))^2*‖a‖^2

theorem continuous_sourceM1ActionScale (w : SpectralWeight) : Continuous (sourceM1ActionScale w) := by
  have he : Continuous (fun a : CoeffPair 2 => w.realExtension (16*‖a‖^2)) :=
    w.continuous_realExtension.comp (continuous_const.mul (continuous_norm.pow 2))
  exact (he.pow 2).mul (continuous_norm.pow 2)

/-- Near every real weighted source, the actual weighted actions form a norm-continuous
complex ℓ¹ map. This proves summability as well as continuity of its norm. -/
theorem exists_local_sourceM1Action_continuousMap (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : realTypeSourceSubmodule 2) :
    ∃ V : Set (CoeffPair 2), IsOpen V ∧ a.val ∈ V ∧ ∃ F : CoeffPair 2 → Coeff 1,
      ContinuousOn F V ∧ ∀ b ∈ V,
        Summable (sourceM1ActionTerm w (normalizedWeightedSource w b)) ∧
        (∀ n : ℤ, F b n = sourceM1ActionCoefficient w (normalizedWeightedSource w b) n) ∧
        ‖F b‖ = ∑' n : ℤ, sourceM1ActionTerm w (normalizedWeightedSource w b) n := by
  classical
  let ψ := normalizedWeightedSource w a.val
  have hψ : IsRealType (CoeffPair.toMax 2 ψ) := normalizedWeightedSource_realType w a.val a.property
  obtain ⟨U,hU,hψU,K,hK,hact,hgap⟩ := exists_local_sourceAction_gap_bound ψ hψ
  let bnd : CoeffPair 2 → ℝ := fun b =>
    K*(265*Real.pi^2*(w.realExtension (16*‖b‖^2))^2*(1+‖b‖^2)*‖b‖^2)
  have hc : Continuous bnd := by
    have he : Continuous (fun b : CoeffPair 2 => w.realExtension (16*‖b‖^2)) :=
      w.continuous_realExtension.comp (continuous_const.mul (continuous_norm.pow 2))
    exact continuous_const.mul (((continuous_const.mul (he.pow 2)).mul
      (continuous_const.add (continuous_norm.pow 2))).mul (continuous_norm.pow 2))
  let V := (normalizedWeightedSource w ⁻¹' (U ∩ sourceSpectralStripNeighborhood (by simp))) ∩
    {b | bnd b < bnd a.val+1}
  have hV : IsOpen V := ((hU.inter (isOpen_sourceSpectralStripNeighborhood (by simp))).preimage
    (continuous_normalizedWeightedSource w)).inter (isOpen_lt hc continuous_const)
  have haV : a.val ∈ V := ⟨⟨hψU,real_mem_sourceSpectralStripNeighborhood (by simp) (by norm_num) ψ hψ⟩,
    by dsimp; linarith⟩
  have hdata (b : CoeffPair 2) (hb : b ∈ V) :=
    sourceM1_complex_actions_summable_and_le w hw b hb.1.2 K hK (hgap _ hb.1.1)
  let F : CoeffPair 2 → Coeff 1 := fun b => if hb : b ∈ V then
    sourceM1ActionSequence w (normalizedWeightedSource w b) (hdata b hb).1 else 0
  have hval (b : CoeffPair 2) (hb : b ∈ V) (n : ℤ) :
      F b n = sourceM1ActionCoefficient w (normalizedWeightedSource w b) n := by
    simp only [F,dif_pos hb,sourceM1ActionSequence_apply]
  have hnorm (b : CoeffPair 2) (hb : b ∈ V) :
      ‖F b‖ = ∑' n : ℤ, sourceM1ActionTerm w (normalizedWeightedSource w b) n := by
    simp only [F,dif_pos hb,sourceM1ActionSequence_norm]
  refine ⟨V,hV,haV,F,?_,fun b hb => ⟨(hdata b hb).1,hval b hb,hnorm b hb⟩⟩
  apply Coeff.continuousOn_of_bounded_coordinatewise (by simp) F hV _ (bnd a.val+1)
    (fun b hb => by rw [hnorm b hb]; exact (hdata b hb).2.trans hb.2.le)
  intro n b hb
  have hd : DifferentiableAt ℂ (fun c : CoeffPair 2 =>
      sourceM1ActionCoefficient w (normalizedWeightedSource w c) n) b := by
    unfold sourceM1ActionCoefficient
    exact (((hact n _ hb.1.1).differentiableAt).comp b
      (normalizedWeightedSourceCLM w).differentiableAt).const_mul _
  have he : (fun c => sourceM1ActionCoefficient w (normalizedWeightedSource w c) n) =ᶠ[𝓝 b]
      (fun c => F c n) := by
    filter_upwards [hV.mem_nhds hb] with c hc
    exact (hval c hc n).symm
  exact (hd.congr_of_eventuallyEq he.symm).differentiableWithinAt

/-- Continuity of the literal weighted absolute action sum at every real source. -/
theorem continuousAt_sourceM1ActionTotal (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : realTypeSourceSubmodule 2) :
    ContinuousAt (fun b : CoeffPair 2 => ∑' n : ℤ,
      sourceM1ActionTerm w (normalizedWeightedSource w b) n) a.val := by
  obtain ⟨V,hV,haV,F,hF,hdata⟩ := exists_local_sourceM1Action_continuousMap w hw a
  apply ((hF a.val haV).continuousAt (hV.mem_nhds haV)).norm.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds haV] with b hb
  exact (hdata b hb).2.2.symm

end NLS.ZakharovShabat
