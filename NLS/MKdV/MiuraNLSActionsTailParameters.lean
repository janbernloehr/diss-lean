import NLS.MKdV.MiuraNLSActionsCartesianStationarity
import NLS.SequenceSpaces.PositiveCartesianParameters
import NLS.SequenceSpaces.LocalTailActionFactor

/-! # Tail quotient parameters for the original NLS action sequence

All positive Cartesian coordinates are normalized in l2. The first zero
entry retains the signed mean linearly. The original whole NLS action
sequence descends analytically to the squared tail sums and this head.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.MKdV.MiuraCartesianNLSActionChart

def parameterObservables (C : MiuraCartesianNLSActionChart) (z : Coeff 2 × Coeff 2) : Coeff 1 :=
  C.observables (WeightedCoeff.positiveCartesianParameterMap (Weight.sobolev (1/2)) 2 z)

/-- One parameter ball works for every original signed NLS action and
every tail mode. The signed mean at index zero is not rotated. -/
theorem exists_parameterObservables_ball (C : MiuraCartesianNLSActionChart) :
    ∃ R : ℝ, 0 < R ∧
      (∀ z ∈ ball 0 R, WeightedCoeff.positiveCartesianParameterMap (Weight.sobolev (1/2)) 2 z ∈ ball 0 C.radius) ∧
      AnalyticOnNhd ℂ C.parameterObservables (ball 0 R) ∧
      ∀ z ∈ ball 0 R, ∀ k : ℤ, k ≠ 0 →
        fderiv ℂ C.parameterObservables z (Coeff.actionRotationVectorCLM 2 k z) = 0 := by
  let E := WeightedCoeff.positiveCartesianParameterMap (Weight.sobolev (1/2)) 2
  have hopen : IsOpen (E ⁻¹' ball 0 C.radius) := isOpen_ball.preimage E.continuous
  have hzero : (0 : Coeff 2 × Coeff 2) ∈ E ⁻¹' ball 0 C.radius := by
    simpa only [mem_preimage,map_zero] using mem_ball_self C.radius_pos
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  have hf : AnalyticOnNhd ℂ C.parameterObservables (ball 0 R) := by
    intro z hz
    exact (C.observables_analytic _ (hball hz)).comp (E.analyticAt z)
  refine ⟨R,hR,hball,hf,?_⟩
  intro z hz k hk
  have hd := (C.observables_analytic _ (hball hz)).differentiableAt.hasFDerivAt.comp z E.hasFDerivAt
  change fderiv ℂ (C.observables ∘ E) z (Coeff.actionRotationVectorCLM 2 k z) = 0
  rw [hd.fderiv]
  change fderiv ℂ C.observables (E z) (E (Coeff.actionRotationVectorCLM 2 k z)) = 0
  rw [WeightedCoeff.positiveCartesianParameterMap_rotationVector _ _ k hk z]
  split_ifs with hkp
  · rw [map_neg]
    have hi : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hkp.le
    have hn : 1 ≤ k.toNat := by omega
    have hstat := C.observables_rotation_stationary k.toNat hn (E z) (hball hz)
    change fderiv ℂ C.observables (E z)
      (WeightedCoeff.positiveCartesianActionVector (Weight.sobolev (1/2)) 2 k.toNat (E z)) = 0 at hstat
    rw [hi] at hstat
    rw [hstat,neg_zero]
  · exact map_zero _

/-- The entire original NLS action sequence has a common local analytic
factor through the tail radii, retaining both zero entries linearly. -/
theorem exists_parameterObservables_tail_factor (C : MiuraCartesianNLSActionChart) :
    ∃ Z : Set (Coeff 2 × Coeff 2), ∃ T : Set (Coeff.TailSumSpace 1 {0}),
      ∃ g : Coeff.TailSumSpace 1 {0} → Coeff 1,
      IsOpen Z ∧ (0 : Coeff 2 × Coeff 2) ∈ Z ∧ IsOpen T ∧
      (fun z => Coeff.tailSumCLM {0} (Coeff.pairMixedSquare (q := 1) {0} z)) '' Z = T ∧
      AnalyticOnNhd ℂ g T ∧
      (∀ z ∈ Z, WeightedCoeff.positiveCartesianParameterMap (Weight.sobolev (1/2)) 2 z ∈ ball 0 C.radius) ∧
      ∀ z ∈ Z, g (Coeff.tailSumCLM {0} (Coeff.pairMixedSquare (q := 1) {0} z)) = C.parameterObservables z := by
  obtain ⟨R,hR,hball,hf,hrot⟩ := C.exists_parameterObservables_ball
  obtain ⟨Z,T,g,hZ,h0Z,hZball,hT,himage,hg,he⟩ :=
    Coeff.exists_local_tail_action_factor (q := 1) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      {0} C.parameterObservables R hR hf (fun z hz k hk => hrot z hz k (by simpa using hk))
  exact ⟨Z,T,g,hZ,h0Z,hT,himage,hg,fun z hz => hball z (hZball hz),he⟩

end NLS.MKdV.MiuraCartesianNLSActionChart
