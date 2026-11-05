import NLS.MKdV.MiuraQuadraticActionParameters
import NLS.MKdV.MiuraCartesianPhaseSaturation
import NLS.SequenceSpaces.RealActionLifting

/-! # Nearby real Cartesian lifts of nearby attained physical action data -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV
local instance : (2 : ℝ≥0∞).HolderTriple 2 1 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

def miuraCartesianPairParameters : MiuraPositiveCartesianTarget →L[ℂ] (Coeff 2 × Coeff 2) :=
  ((WeightedCoeff.positiveToCoeff (Weight.sobolev (1/2)) 2).prodMap
    (WeightedCoeff.positiveToCoeff (Weight.sobolev (1/2)) 2)).comp (ContinuousLinearMap.fst ℂ _ ℂ)

def miuraCartesianFromPairMean : ((Coeff 2 × Coeff 2) × ℂ) →L[ℂ] MiuraPositiveCartesianTarget :=
  ((WeightedCoeff.positiveFromCoeff (Weight.sobolev (1/2)) 2).prodMap
    (WeightedCoeff.positiveFromCoeff (Weight.sobolev (1/2)) 2)).prodMap (ContinuousLinearMap.id ℂ ℂ)

theorem miuraCartesianFromPairMean_parameters (z : MiuraPositiveCartesianTarget) :
    miuraCartesianFromPairMean (miuraCartesianPairParameters z,z.2) = z := by
  apply WeightedCoeff.positivePairMean_ext
  · intro n hn
    change ((WeightedCoeff.positiveFromCoeff (Weight.sobolev (1/2)) 2
        (WeightedCoeff.positiveToCoeff (Weight.sobolev (1/2)) 2 z.1.1)).val.val n,
      (WeightedCoeff.positiveFromCoeff (Weight.sobolev (1/2)) 2
        (WeightedCoeff.positiveToCoeff (Weight.sobolev (1/2)) 2 z.1.2)).val.val n) = _
    rw [WeightedCoeff.positiveFromCoeff_apply,WeightedCoeff.positiveFromCoeff_apply,
      if_pos hn,if_pos hn,WeightedCoeff.positiveToCoeff_apply,WeightedCoeff.positiveToCoeff_apply,
      mul_div_cancel_left₀ _ ((Weight.sobolev (1/2)).complex_ne_zero n),
      mul_div_cancel_left₀ _ ((Weight.sobolev (1/2)).complex_ne_zero n)]
  · rfl

theorem miuraCartesianPairParameters_fromPairMean (q : Coeff 2 × Coeff 2) (c : ℂ) (n : ℤ) :
    ((miuraCartesianPairParameters (miuraCartesianFromPairMean (q,c))).1 n,
      (miuraCartesianPairParameters (miuraCartesianFromPairMean (q,c))).2 n) =
      if 0 < n then (q.1 n,q.2 n) else 0 := by
  change ((Weight.sobolev (1/2) n : ℂ)*
      (WeightedCoeff.positiveFromCoeff (Weight.sobolev (1/2)) 2 q.1).val.val n,
    (Weight.sobolev (1/2) n : ℂ)*
      (WeightedCoeff.positiveFromCoeff (Weight.sobolev (1/2)) 2 q.2).val.val n) = _
  rw [WeightedCoeff.positiveFromCoeff_apply,WeightedCoeff.positiveFromCoeff_apply]
  by_cases hn : 0 < n
  · rw [if_pos hn,if_pos hn,if_pos hn,
      mul_div_cancel₀ _ ((Weight.sobolev (1/2)).complex_ne_zero n),
      mul_div_cancel₀ _ ((Weight.sobolev (1/2)).complex_ne_zero n)]
  · simp only [if_neg hn,mul_zero]
    rfl

theorem miuraCartesianPairParameters_real (z : MiuraRealCartesianTarget) :
    miuraCartesianPairParameters z.val ∈ Coeff.realPairLocus 2 := by
  constructor <;> intro n
  · change ((Weight.sobolev (1/2) n : ℂ)*z.val.1.1.val.val n).im = 0
    simp [Complex.mul_im,(z.property.1 n).1]
  · change ((Weight.sobolev (1/2) n : ℂ)*z.val.1.2.val.val n).im = 0
    simp [Complex.mul_im,(z.property.1 n).2]

theorem miuraCartesianFromPairMean_real (q : Coeff 2 × Coeff 2) (hq : q ∈ Coeff.realPairLocus 2)
    (c : ℂ) (hc : c.im = 0) : miuraCartesianFromPairMean (q,c) ∈ miuraCartesianRealSubmodule := by
  refine ⟨?_,hc⟩
  intro n
  change ((WeightedCoeff.positiveFromCoeff (Weight.sobolev (1/2)) 2 q.1).val.val n).im = 0 ∧
    ((WeightedCoeff.positiveFromCoeff (Weight.sobolev (1/2)) 2 q.2).val.val n).im = 0
  rw [WeightedCoeff.positiveFromCoeff_apply,WeightedCoeff.positiveFromCoeff_apply]
  by_cases hn : 0 < n
  · simp [if_pos hn,Complex.div_im,hq.1 n,hq.2 n]
  · simp only [if_neg hn,Complex.zero_im,and_self]

theorem miuraCartesianPairParameters_actions (z : MiuraPositiveCartesianTarget) :
    quadraticActionsExponent (q := 1) (miuraCartesianPairParameters z) =
      WeightedCoeff.weightIsometry (Weight.sobolev 1) 1 (miuraPositiveCartesianActionMean z).1 := by
  ext n
  rw [quadraticActionsExponent_apply]
  change (((Weight.sobolev (1/2) n : ℂ)*z.1.1.val.val n)^2+
      ((Weight.sobolev (1/2) n : ℂ)*z.1.2.val.val n)^2)/2 =
    (Weight.sobolev 1 n : ℂ)*(miuraL2CartesianActions (z.1.1.val,z.1.2.val)).val n
  rw [miuraL2CartesianActions_apply,mul_pow,mul_pow]
  have hw : (Weight.sobolev (1/2) n : ℂ)^2 = (Weight.sobolev 1 n : ℂ) := by
    have he : Weight.sobolev (1/2) n*Weight.sobolev (1/2) n = Weight.sobolev 1 n := by
      rw [Weight.sobolev_apply,← Real.rpow_add (by positivity)]
      norm_num
    simpa only [pow_two,Complex.ofReal_mul] using congrArg (fun t : ℝ => (t : ℂ)) he
  rw [hw]
  ring

theorem miuraNormalizedActions_nonnegative (a : MiuraRealL2) :
    WeightedCoeff.weightIsometry (Weight.sobolev 1) 1 (miuraRealL2ActionMeanMap a).1 ∈ Coeff.nonnegativeLocus 1 := by
  have h := miuraCartesianPairParameters_actions (miuraPositiveCartesianMap a.val)
  rw [miuraPositiveCartesianActionMean_map a.val a.property] at h
  change WeightedCoeff.weightIsometry (Weight.sobolev 1) 1 (miuraL2ActionMeanMap a.val).1 ∈ Coeff.nonnegativeLocus 1
  rw [← h]
  exact Coeff.quadraticActions_mem_nonnegativeLocus _
    (miuraCartesianPairParameters_real ⟨_,miuraPositiveCartesianMap_physicalReal a⟩)

theorem miuraCartesianFromPairMean_action_of_quadratic (q : Coeff 2 × Coeff 2) (b : MiuraRealL2)
    (hquad : quadraticActionsExponent (q := 1) q =
      WeightedCoeff.weightIsometry (Weight.sobolev 1) 1 (miuraRealL2ActionMeanMap b).1) :
    miuraPositiveCartesianActionMean (miuraCartesianFromPairMean (q,(miuraRealL2ActionMeanMap b).2)) =
      miuraRealL2ActionMeanMap b := by
  apply Prod.ext
  · apply (WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).injective
    rw [← miuraCartesianPairParameters_actions]
    ext n
    have hp := miuraCartesianPairParameters_fromPairMean q (miuraRealL2ActionMeanMap b).2 n
    rw [quadraticActionsExponent_apply]
    by_cases hn : 0 < n
    · rw [if_pos hn] at hp
      have hx := congrArg Prod.fst hp
      have hy := congrArg Prod.snd hp
      change (miuraCartesianPairParameters (miuraCartesianFromPairMean (q,(miuraRealL2ActionMeanMap b).2))).1 n = q.1 n at hx
      change (miuraCartesianPairParameters (miuraCartesianFromPairMean (q,(miuraRealL2ActionMeanMap b).2))).2 n = q.2 n at hy
      rw [hx,hy]
      simpa only [quadraticActionsExponent_apply] using congrArg (fun v : Coeff 1 => v n) hquad
    · rw [if_neg hn] at hp
      have hx := congrArg Prod.fst hp
      have hy := congrArg Prod.snd hp
      change (miuraCartesianPairParameters (miuraCartesianFromPairMean (q,(miuraRealL2ActionMeanMap b).2))).1 n = 0 at hx
      change (miuraCartesianPairParameters (miuraCartesianFromPairMean (q,(miuraRealL2ActionMeanMap b).2))).2 n = 0 at hy
      rw [hx,hy]
      change (0^2+0^2)/2 = (Weight.sobolev 1 n : ℂ)*(miuraL2ActionSequence b.val).val n
      rw [miuraL2ActionSequence_nonpositive b.val n hn]
      ring
  · rfl

/-- Every open real Cartesian neighborhood realizes an open neighborhood
of its physical action/mean data among attained physical L2 data. -/
theorem exists_miuraCartesian_real_action_lift_neighborhood (z : MiuraRealCartesianTarget)
    (W : Set MiuraPositiveCartesianTarget) (hW : IsOpen W) (hzW : z.val ∈ W) :
    ∃ V : Set MiuraActionMeanTarget, IsOpen V ∧ miuraPositiveCartesianActionMean z.val ∈ V ∧
      ∀ b : MiuraRealL2, miuraRealL2ActionMeanMap b ∈ V →
        ∃ v ∈ W, v ∈ miuraCartesianRealSubmodule ∧ miuraPositiveCartesianActionMean v = miuraRealL2ActionMeanMap b := by
  let q₀ := miuraCartesianPairParameters z.val
  let N : MiuraActionMeanTarget →L[ℂ] Coeff 1 :=
    (WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℂ _ ℂ)
  have hbase : (q₀,z.val.2) ∈ miuraCartesianFromPairMean ⁻¹' W := by
    change miuraCartesianFromPairMean (miuraCartesianPairParameters z.val,z.val.2) ∈ W
    rwa [miuraCartesianFromPairMean_parameters]
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp (hW.preimage miuraCartesianFromPairMean.continuous) _ hbase
  obtain ⟨r,hr,hlift⟩ := Coeff.exists_ball_real_quadraticActions_lifts (q := 1)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) q₀ (miuraCartesianPairParameters_real z) (ball q₀ R) isOpen_ball (mem_ball_self hR)
  let V := N ⁻¹' ball (quadraticActionsExponent (q := 1) q₀) r ∩
    (fun b : MiuraActionMeanTarget => b.2) ⁻¹' ball z.val.2 R
  have hV : IsOpen V := (isOpen_ball.preimage N.continuous).inter (isOpen_ball.preimage continuous_snd)
  have hcenter : miuraPositiveCartesianActionMean z.val ∈ V := by
    refine ⟨?_,mem_ball_self hR⟩
    change N (miuraPositiveCartesianActionMean z.val) ∈ ball (quadraticActionsExponent (q := 1) q₀) r
    rw [miuraCartesianPairParameters_actions]
    exact mem_ball_self hr
  refine ⟨V,hV,hcenter,?_⟩
  intro b hb
  obtain ⟨q,⟨hq,hqr⟩,hquad⟩ := hlift ⟨hb.1,miuraNormalizedActions_nonnegative b⟩
  let v := miuraCartesianFromPairMean (q,(miuraRealL2ActionMeanMap b).2)
  have hvW : v ∈ W := by
    apply hball
    change max (dist q q₀) (dist (miuraRealL2ActionMeanMap b).2 z.val.2) < R
    exact max_lt hq hb.2
  refine ⟨v,hvW,miuraCartesianFromPairMean_real q hqr _ (miuraPositiveCartesianMap_physicalReal b).2,?_⟩
  exact miuraCartesianFromPairMean_action_of_quadratic q b hquad

end NLS.MKdV
