import NLS.MKdV.MiuraGeneralNLSActionsCartesianStationarity
import NLS.MKdV.MiuraQuadraticActionParameters
import NLS.SequenceSpaces.LocalSequenceActionDescent

/-! # Forward action factorization at every original real H1 profile

The zero auxiliary action is the literal signed mean. Its isotropic
entire section removes any sign or zero-mean branch restriction. Full
sequence-valued action descent applies at arbitrary complex parameters.
-/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV
local instance : (2 : ℝ≥0∞).HolderTriple 2 1 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

namespace MiuraGeneralCartesianNLSActionChart
variable {a : MiuraRealL2}

def quadraticParameterObservables (C : MiuraGeneralCartesianNLSActionChart a) (z : Coeff 2 × Coeff 2) : Coeff 1 :=
  C.observables (WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2)) z)

def quadraticParameterDomain (C : MiuraGeneralCartesianNLSActionChart a) : Set (Coeff 2 × Coeff 2) :=
  (WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2))) ⁻¹'
    ball (miuraPositiveCartesianMap a.val) C.radius

theorem quadraticParameterDomain_open (C : MiuraGeneralCartesianNLSActionChart a) :
    IsOpen C.quadraticParameterDomain := isOpen_ball.preimage
  (continuous_iff_continuousAt.mpr (fun z =>
    (WeightedCoeff.analyticAt_positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2)) z).continuousAt))

theorem quadraticParameterObservables_analytic (C : MiuraGeneralCartesianNLSActionChart a) :
    AnalyticOnNhd ℂ C.quadraticParameterObservables C.quadraticParameterDomain := by
  intro z hz
  exact (C.observables_analytic _ hz).comp
    (WeightedCoeff.analyticAt_positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2)) z)

/-- All auxiliary rotations, including at index zero, are stationary.
The zero quadratic action represents signed mean, not mean squared. -/
theorem quadraticParameterObservables_stationary (C : MiuraGeneralCartesianNLSActionChart a)
    (z : Coeff 2 × Coeff 2) (hz : z ∈ C.quadraticParameterDomain) (k : ℤ) :
    fderiv ℂ C.quadraticParameterObservables z (Coeff.actionRotationVectorCLM 2 k z) = 0 := by
  let A := WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2))
  have hd := (C.observables_analytic (A z) hz).differentiableAt.hasFDerivAt.comp z
    (WeightedCoeff.hasFDerivAt_positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2)) z)
  change fderiv ℂ (C.observables ∘ A) z _ = 0
  rw [hd.fderiv]
  change fderiv ℂ C.observables (A z)
    (WeightedCoeff.positiveCartesianQuadraticMeanDerivative (Weight.sobolev (1/2)) z
      (Coeff.actionRotationVectorCLM 2 k z)) = 0
  rw [WeightedCoeff.positiveCartesianQuadraticMeanDerivative_rotation]
  by_cases hk : 0 < k
  · rw [if_pos hk,map_neg]
    have hs := C.observables_rotation_stationary k.toNat (by omega) (A z) hz
    change fderiv ℂ C.observables (A z)
      (WeightedCoeff.positiveCartesianActionVector (Weight.sobolev (1/2)) 2 (k.toNat : ℤ) (A z)) = 0 at hs
    rw [Int.toNat_of_nonneg hk.le] at hs
    rw [hs,neg_zero]
  · rw [if_neg hk,map_zero]

/-- Near the image of the basepoint, the whole original NLS action
sequence has a holomorphic factor through native physical actions and
the literal signed mean on full open complex action neighborhoods. -/
theorem exists_native_action_factor (C : MiuraGeneralCartesianNLSActionChart a) :
    ∃ W : Set MiuraPositiveCartesianTarget, ∃ V : Set MiuraActionMeanTarget,
      ∃ F : MiuraActionMeanTarget → Coeff 1,
        IsOpen W ∧ miuraPositiveCartesianMap a.val ∈ W ∧
          W ⊆ ball (miuraPositiveCartesianMap a.val) C.radius ∧ IsOpen V ∧
          miuraPositiveCartesianActionMean (miuraPositiveCartesianMap a.val) ∈ V ∧
          AnalyticOnNhd ℂ F V ∧ ∀ z ∈ W, miuraPositiveCartesianActionMean z ∈ V ∧
            F (miuraPositiveCartesianActionMean z) = C.observables z := by
  let L := WeightedCoeff.positiveCartesianIsotropicSection (Weight.sobolev (1/2))
  let q := L (miuraPositiveCartesianMap a.val)
  have hq : q ∈ C.quadraticParameterDomain := by
    change WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2))
      (L (miuraPositiveCartesianMap a.val)) ∈ ball (miuraPositiveCartesianMap a.val) C.radius
    rw [WeightedCoeff.positiveCartesianQuadraticMeanMap_isotropicSection]
    exact mem_ball_self C.radius_pos
  obtain ⟨Z,T,g,hZ,hqZ,_,hT,himage,hg,hrec⟩ :=
    Coeff.exists_local_sequence_action_factor_of_stationarity (q := 1) (by simp : (2 : ℝ≥0∞) ≠ ⊤)
      C.quadraticParameterObservables C.quadraticParameterDomain C.quadraticParameterDomain_open
      C.quadraticParameterObservables_analytic C.quadraticParameterObservables_stationary q hq
  let W := ball (miuraPositiveCartesianMap a.val) C.radius ∩ L ⁻¹' Z
  let V := miuraActionQuadraticParameters ⁻¹' T
  have hL : Continuous L := continuous_iff_continuousAt.mpr
    (fun z => (WeightedCoeff.analyticAt_positiveCartesianIsotropicSection (Weight.sobolev (1/2)) z).continuousAt)
  have hbase : miuraActionQuadraticParameters
      (miuraPositiveCartesianActionMean (miuraPositiveCartesianMap a.val)) ∈ T := by
    rw [← miuraCartesian_quadratic_parameters,← himage]
    exact ⟨q,hqZ,rfl⟩
  refine ⟨W,V,fun b => g (miuraActionQuadraticParameters b),
    isOpen_ball.inter (hZ.preimage hL),⟨mem_ball_self C.radius_pos,hqZ⟩,
    inter_subset_left,hT.preimage miuraActionQuadraticParameters.continuous,hbase,
    fun b hb => (hg _ hb).comp (miuraActionQuadraticParameters.analyticAt b),?_⟩
  intro z hz
  have hmem : miuraActionQuadraticParameters (miuraPositiveCartesianActionMean z) ∈ T := by
    rw [← miuraCartesian_quadratic_parameters,← himage]
    exact ⟨L z,hz.2,rfl⟩
  refine ⟨hmem,?_⟩
  change g (miuraActionQuadraticParameters (miuraPositiveCartesianActionMean z)) = C.observables z
  rw [← miuraCartesian_quadratic_parameters,hrec (L z) hz.2]
  change C.observables (WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2)) (L z)) = _
  rw [WeightedCoeff.positiveCartesianQuadraticMeanMap_isotropicSection]

end MiuraGeneralCartesianNLSActionChart

/-- The full forward analytic action factor exists near every original
physical real H1 input, including zero mean and all collapsed gaps. -/
theorem exists_local_miura_original_NLS_action_factor_at_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ U : Set (Coeff 2), ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen U ∧ scalarInclusion a ∈ U ∧ IsOpen V ∧ miuraL2ActionMeanMap (scalarInclusion a) ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ b ∈ U, (∀ j, b j = conj (b (-j))) →
        miuraL2ActionMeanMap b ∈ V ∧ F (miuraL2ActionMeanMap b) = miuraOriginalNLSActionSequence b := by
  let b := miuraPhysicalH1L2Point a ha
  obtain ⟨C⟩ := nonempty_miuraGeneralCartesianNLSActionChart a ha
  obtain ⟨W,V,F,hW,hbaseW,_,hV,hbaseV,hF,hrec⟩ := C.exists_native_action_factor
  let U := C.source ∩ miuraPositiveCartesianMap ⁻¹' W
  have hU : IsOpen U := C.forward_analytic.continuousOn.isOpen_inter_preimage C.source_open hW
  have hbase : miuraL2ActionMeanMap (scalarInclusion a) ∈ V := by
    change miuraPositiveCartesianActionMean (miuraPositiveCartesianMap b.val) ∈ V at hbaseV
    rw [miuraPositiveCartesianActionMean_map b.val b.property] at hbaseV
    exact hbaseV
  refine ⟨U,V,F,hU,⟨C.source_base,hbaseW⟩,hV,hbase,hF,?_⟩
  intro v hv hvr
  obtain ⟨hmem,he⟩ := hrec (miuraPositiveCartesianMap v) hv.2
  rw [miuraPositiveCartesianActionMean_map v hvr] at hmem he
  exact ⟨hmem,he.trans (C.observables_recover v hv.1)⟩

end NLS.MKdV
