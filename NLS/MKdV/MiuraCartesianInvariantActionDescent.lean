import NLS.MKdV.MiuraQuadraticActionParameters
import NLS.SequenceSpaces.LocalSequenceActionDescent

/-! # Local analytic Cartesian invariants descend to actions and literal mean -/
noncomputable section
open Set Metric Complex
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV
local instance : (2 : ℝ≥0∞).HolderTriple 2 1 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

private theorem quadratic_observable_stationary {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (f : MiuraPositiveCartesianTarget → Coeff r) (O : Set MiuraPositiveCartesianTarget)
    (hf : AnalyticOnNhd ℂ f O)
    (hrot : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ O, fderiv ℂ f z (miuraCartesianActionVector n z) = 0)
    (z : Coeff 2 × Coeff 2) (hz : z ∈ ((WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2))) ⁻¹' O)) (k : ℤ) :
    fderiv ℂ (fun z => f (WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2)) z)) z (Coeff.actionRotationVectorCLM 2 k z) = 0 := by
  let A := WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2))
  have hd := (hf (A z) hz).differentiableAt.hasFDerivAt.comp z
    (WeightedCoeff.hasFDerivAt_positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2)) z)
  change fderiv ℂ (f ∘ A) z _ = 0
  rw [hd.fderiv]
  change fderiv ℂ f (A z)
    (WeightedCoeff.positiveCartesianQuadraticMeanDerivative (Weight.sobolev (1/2)) z
      (Coeff.actionRotationVectorCLM 2 k z)) = 0
  rw [WeightedCoeff.positiveCartesianQuadraticMeanDerivative_rotation]
  by_cases hk : 0 < k
  · rw [if_pos hk,map_neg]
    have hs := hrot k.toNat (by omega) (A z) hz
    change fderiv ℂ f (A z)
      (WeightedCoeff.positiveCartesianActionVector (Weight.sobolev (1/2)) 2 (k.toNat : ℤ) (A z)) = 0 at hs
    rw [Int.toNat_of_nonneg hk.le] at hs
    rw [hs,neg_zero]
  · rw [if_neg hk,map_zero]

/-- Any sequence-valued holomorphic Cartesian rotation invariant has a
local holomorphic factor through the whole action sequence and signed mean. -/
theorem exists_local_miuraCartesian_action_factor {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (f : MiuraPositiveCartesianTarget → Coeff r) (O : Set MiuraPositiveCartesianTarget)
    (hO : IsOpen O) (hf : AnalyticOnNhd ℂ f O)
    (hrot : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ O, fderiv ℂ f z (miuraCartesianActionVector n z) = 0)
    (z₀ : MiuraPositiveCartesianTarget) (hz₀ : z₀ ∈ O) :
    ∃ W : Set MiuraPositiveCartesianTarget, ∃ V : Set MiuraActionMeanTarget,
      ∃ F : MiuraActionMeanTarget → Coeff r,
        IsOpen W ∧ z₀ ∈ W ∧ W ⊆ O ∧ IsOpen V ∧ miuraPositiveCartesianActionMean z₀ ∈ V ∧
          AnalyticOnNhd ℂ F V ∧ ∀ z ∈ W, miuraPositiveCartesianActionMean z ∈ V ∧
            F (miuraPositiveCartesianActionMean z) = f z := by
  let A := WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2))
  let Q := A ⁻¹' O
  have hQ : IsOpen Q := hO.preimage (continuous_iff_continuousAt.mpr
    (fun z => (WeightedCoeff.analyticAt_positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2)) z).continuousAt))
  have hQA : AnalyticOnNhd ℂ (fun z => f (A z)) Q := fun z hz =>
    (hf _ hz).comp (WeightedCoeff.analyticAt_positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2)) z)
  let L := WeightedCoeff.positiveCartesianIsotropicSection (Weight.sobolev (1/2))
  let q := L (z₀)
  have hq : q ∈ ((WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2))) ⁻¹' O) := by
    change WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2))
      (L (z₀)) ∈ O
    rw [WeightedCoeff.positiveCartesianQuadraticMeanMap_isotropicSection]
    exact hz₀
  obtain ⟨Z,T,g,hZ,hqZ,_,hT,himage,hg,hrec⟩ :=
    Coeff.exists_local_sequence_action_factor_of_stationarity (q := 1) (by simp : (2 : ℝ≥0∞) ≠ ⊤)
      (fun z => f (WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2)) z)) ((WeightedCoeff.positiveCartesianQuadraticMeanMap (Weight.sobolev (1/2))) ⁻¹' O) hQ
      hQA (quadratic_observable_stationary f O hf hrot) q hq
  let W := O ∩ L ⁻¹' Z
  let V := miuraActionQuadraticParameters ⁻¹' T
  have hL : Continuous L := continuous_iff_continuousAt.mpr
    (fun z => (WeightedCoeff.analyticAt_positiveCartesianIsotropicSection (Weight.sobolev (1/2)) z).continuousAt)
  have hbase : miuraActionQuadraticParameters
      (miuraPositiveCartesianActionMean (z₀)) ∈ T := by
    rw [← miuraCartesian_quadratic_parameters,← himage]
    exact ⟨q,hqZ,rfl⟩
  refine ⟨W,V,fun b => g (miuraActionQuadraticParameters b),
    hO.inter (hZ.preimage hL),⟨hz₀,hqZ⟩,
    inter_subset_left,hT.preimage miuraActionQuadraticParameters.continuous,hbase,
    fun b hb => (hg _ hb).comp (miuraActionQuadraticParameters.analyticAt b),?_⟩
  intro z hz
  have hmem : miuraActionQuadraticParameters (miuraPositiveCartesianActionMean z) ∈ T := by
    rw [← miuraCartesian_quadratic_parameters,← himage]
    exact ⟨L z,hz.2,rfl⟩
  refine ⟨hmem,?_⟩
  change g (miuraActionQuadraticParameters (miuraPositiveCartesianActionMean z)) = f z
  rw [← miuraCartesian_quadratic_parameters,hrec (L z) hz.2]
  rw [WeightedCoeff.positiveCartesianQuadraticMeanMap_isotropicSection]


/-- Scalar-valued Cartesian invariants have the same local analytic
factor through all positive actions and the literal signed mean. -/
theorem exists_local_scalar_miuraCartesian_action_factor
    (f : MiuraPositiveCartesianTarget → ℂ) (O : Set MiuraPositiveCartesianTarget)
    (hO : IsOpen O) (hf : AnalyticOnNhd ℂ f O)
    (hrot : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ O, fderiv ℂ f z (miuraCartesianActionVector n z) = 0)
    (z₀ : MiuraPositiveCartesianTarget) (hz₀ : z₀ ∈ O) :
    ∃ W : Set MiuraPositiveCartesianTarget, ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → ℂ,
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ O ∧ IsOpen V ∧ miuraPositiveCartesianActionMean z₀ ∈ V ∧
        AnalyticOnNhd ℂ F V ∧ ∀ z ∈ W, miuraPositiveCartesianActionMean z ∈ V ∧
          F (miuraPositiveCartesianActionMean z) = f z := by
  let L := lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 1 0
  let e := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 0
  have hA : AnalyticOnNhd ℂ (fun z => L (f z)) O := fun z hz => (L.analyticAt _).comp (hf z hz)
  have hr : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ O,
      fderiv ℂ (fun z => L (f z)) z (miuraCartesianActionVector n z) = 0 := by
    intro n hn z hz
    have hd := L.hasFDerivAt.comp z (hf z hz).differentiableAt.hasFDerivAt
    change HasFDerivAt (fun z => L (f z)) _ z at hd
    rw [hd.fderiv]
    change L (fderiv ℂ f z (miuraCartesianActionVector n z)) = 0
    rw [hrot n hn z hz,map_zero]
  obtain ⟨W,V,G,hW,hbase,hWO,hV,hbaseV,hG,hrec⟩ :=
    exists_local_miuraCartesian_action_factor (fun z => L (f z)) O hO hA hr z₀ hz₀
  refine ⟨W,V,fun b => e (G b),hW,hbase,hWO,hV,hbaseV,
    fun b hb => (e.analyticAt _).comp (hG b hb),?_⟩
  intro z hz
  refine ⟨(hrec z hz).1,?_⟩
  change e (G (miuraPositiveCartesianActionMean z)) = f z
  rw [(hrec z hz).2]
  change (lp.single (E := fun _ : ℤ => ℂ) 1 0 (f z)) 0 = f z
  simp only [lp.single_apply,Pi.single_eq_same]


end NLS.MKdV
