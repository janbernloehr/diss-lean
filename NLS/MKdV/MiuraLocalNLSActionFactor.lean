import NLS.MKdV.MiuraNLSActionsTailParameters
import NLS.MKdV.MiuraCartesianActionParameters

/-! # Local forward NLS action factorization through physical actions and mean

The entire original signed NLS action sequence factors analytically near
the free profile through the native physical action sequence and signed
mean. The common neighborhoods include zero mean and every closed gap.
This is a local result; global forward factorization remains separate.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV.MiuraCartesianNLSActionChart

theorem exists_native_action_factor (C : MiuraCartesianNLSActionChart) :
    ∃ W : Set MiuraPositiveCartesianTarget, ∃ V : Set MiuraActionMeanTarget,
      ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen W ∧ (0 : MiuraPositiveCartesianTarget) ∈ W ∧ W ⊆ ball 0 C.radius ∧
      IsOpen V ∧ (0 : MiuraActionMeanTarget) ∈ V ∧ AnalyticOnNhd ℂ F V ∧
      ∀ z ∈ W, miuraPositiveCartesianActionMean z ∈ V ∧
        F (miuraPositiveCartesianActionMean z) = C.observables z := by
  obtain ⟨Z,T,g,hZ,h0Z,hT,himage,hg,_,he⟩ := C.exists_parameterObservables_tail_factor
  let P := WeightedCoeff.positiveCartesianParameterSection (Weight.sobolev (1/2)) 2
  let W := ball (0 : MiuraPositiveCartesianTarget) C.radius ∩ P ⁻¹' Z
  let V := miuraActionTailParameters ⁻¹' T
  have hW : IsOpen W := isOpen_ball.inter (hZ.preimage P.continuous)
  have h0W : (0 : MiuraPositiveCartesianTarget) ∈ W := by
    exact ⟨mem_ball_self C.radius_pos,by simpa only [mem_preimage,map_zero] using h0Z⟩
  have hT0 : (0 : Coeff.TailSumSpace 1 {0}) ∈ T := by
    rw [← himage]
    refine ⟨0,h0Z,?_⟩
    have hzero : Coeff.pairMixedSquare (p := 2) (q := 1) {0} 0 = 0 := by
      apply Prod.ext <;> ext n <;> simp [Coeff.pairMixedSquare,Coeff.mixedSquare_apply]
    change Coeff.tailSumCLM {0} (Coeff.pairMixedSquare (p := 2) (q := 1) {0} 0) = 0
    rw [hzero,map_zero]
  refine ⟨W,V,fun b => g (miuraActionTailParameters b),hW,h0W,fun _ hz => hz.1,
    hT.preimage miuraActionTailParameters.continuous,?_,?_,?_⟩
  · change miuraActionTailParameters 0 ∈ T
    simpa only [map_zero] using hT0
  · intro b hb
    exact (hg _ hb).comp (miuraActionTailParameters.analyticAt b)
  · intro z hz
    have hPz : P z ∈ Z := hz.2
    have hparam := miuraCartesian_tail_parameters z
    have hmem : miuraActionTailParameters (miuraPositiveCartesianActionMean z) ∈ T := by
      rw [← hparam,← himage]
      exact ⟨P z,hPz,rfl⟩
    refine ⟨hmem,?_⟩
    change g (miuraActionTailParameters (miuraPositiveCartesianActionMean z)) = C.observables z
    rw [← hparam,he (P z) hPz]
    change C.observables (WeightedCoeff.positiveCartesianParameterMap (Weight.sobolev (1/2)) 2 (P z)) = _
    rw [WeightedCoeff.positiveCartesianParameterMap_section]

end MiuraCartesianNLSActionChart

/-- Local near-zero analytic forward factorization of the full original
NLS action sequence through the native physical action map and signed mean. -/
theorem exists_local_miura_original_NLS_action_factor :
    ∃ U : Set (Coeff 2), ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen U ∧ (0 : Coeff 2) ∈ U ∧ IsOpen V ∧ (0 : MiuraActionMeanTarget) ∈ V ∧
      AnalyticOnNhd ℂ F V ∧
      ∀ a ∈ U, (∀ j, a j = conj (a (-j))) →
        miuraL2ActionMeanMap a ∈ V ∧ F (miuraL2ActionMeanMap a) = miuraOriginalNLSActionSequence a := by
  obtain ⟨C⟩ := nonempty_miuraCartesianNLSActionChart
  obtain ⟨W,V,F,hW,h0W,_,hV,h0V,hF,he⟩ := C.exists_native_action_factor
  let U := C.source ∩ miuraPositiveCartesianMap ⁻¹' W
  have hU : IsOpen U := C.forward_analytic.continuousOn.isOpen_inter_preimage C.source_open hW
  have h0U : (0 : Coeff 2) ∈ U :=
    ⟨C.source_zero,by simpa only [mem_preimage,miuraPositiveCartesianMap_zero] using h0W⟩
  refine ⟨U,V,F,hU,h0U,hV,h0V,hF,?_⟩
  intro a ha har
  obtain ⟨hmem,hrec⟩ := he (miuraPositiveCartesianMap a) ha.2
  rw [miuraPositiveCartesianActionMean_map a har] at hmem hrec
  exact ⟨hmem,hrec.trans (C.observables_recover a ha.1)⟩

end NLS.MKdV
