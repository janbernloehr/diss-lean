import NLS.MKdV.MiuraCartesianRealActionLifts

/-! # Real Cartesian lifts for arbitrary positive action data and signed mean -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraCartesianFromPairMean_action_of_quadratic_data (q : Coeff 2 × Coeff 2) (b : MiuraActionMeanTarget)
    (hzero : ∀ n : ℤ, ¬0 < n → b.1.val n = 0)
    (hquad : quadraticActionsExponent (q := 1) q =
      WeightedCoeff.weightIsometry (Weight.sobolev 1) 1 b.1) :
    miuraPositiveCartesianActionMean (miuraCartesianFromPairMean (q,b.2)) =
      b := by
  apply Prod.ext
  · apply (WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).injective
    rw [← miuraCartesianPairParameters_actions]
    ext n
    have hp := miuraCartesianPairParameters_fromPairMean q b.2 n
    rw [quadraticActionsExponent_apply]
    by_cases hn : 0 < n
    · rw [if_pos hn] at hp
      have hx := congrArg Prod.fst hp
      have hy := congrArg Prod.snd hp
      change (miuraCartesianPairParameters (miuraCartesianFromPairMean (q,b.2))).1 n = q.1 n at hx
      change (miuraCartesianPairParameters (miuraCartesianFromPairMean (q,b.2))).2 n = q.2 n at hy
      rw [hx,hy]
      simpa only [quadraticActionsExponent_apply] using congrArg (fun v : Coeff 1 => v n) hquad
    · rw [if_neg hn] at hp
      have hx := congrArg Prod.fst hp
      have hy := congrArg Prod.snd hp
      change (miuraCartesianPairParameters (miuraCartesianFromPairMean (q,b.2))).1 n = 0 at hx
      change (miuraCartesianPairParameters (miuraCartesianFromPairMean (q,b.2))).2 n = 0 at hy
      rw [hx,hy]
      change (0^2+0^2)/2 = (Weight.sobolev 1 n : ℂ)*b.1.val n
      rw [hzero n hn]
      ring
  · rfl


theorem miuraCartesian_actionMean_nonpositive (z : MiuraPositiveCartesianTarget) (n : ℤ) (hn : ¬0 < n) :
    (miuraPositiveCartesianActionMean z).1.val n = 0 := by
  change (miuraL2CartesianActions (z.1.1.val,z.1.2.val)).val n = 0
  rw [miuraL2CartesianActions_apply,z.1.1.property n (by omega),z.1.2.property n (by omega)]
  ring

theorem miuraCartesian_normalized_actions_nonnegative (z : MiuraRealCartesianTarget) :
    WeightedCoeff.weightIsometry (Weight.sobolev 1) 1 (miuraPositiveCartesianActionMean z.val).1 ∈
      Coeff.nonnegativeLocus 1 := by
  rw [← miuraCartesianPairParameters_actions]
  exact Coeff.quadraticActions_mem_nonnegativeLocus _ (miuraCartesianPairParameters_real z)

/-- A neighborhood of any real Cartesian point realizes a full action
neighborhood among all real Cartesian data, without a source premise. -/
theorem exists_miuraCartesian_real_target_action_lift_neighborhood (z : MiuraRealCartesianTarget)
    (W : Set MiuraPositiveCartesianTarget) (hW : IsOpen W) (hzW : z.val ∈ W) :
    ∃ V : Set MiuraActionMeanTarget, IsOpen V ∧ miuraPositiveCartesianActionMean z.val ∈ V ∧
      ∀ b : MiuraRealCartesianTarget, miuraPositiveCartesianActionMean b.val ∈ V →
        ∃ v ∈ W, v ∈ miuraCartesianRealSubmodule ∧
          miuraPositiveCartesianActionMean v = miuraPositiveCartesianActionMean b.val := by
  let q₀ := miuraCartesianPairParameters z.val
  let N : MiuraActionMeanTarget →L[ℂ] Coeff 1 :=
    (WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℂ _ ℂ)
  have hbase : (q₀,z.val.2) ∈ miuraCartesianFromPairMean ⁻¹' W := by
    change miuraCartesianFromPairMean (miuraCartesianPairParameters z.val,z.val.2) ∈ W
    rwa [miuraCartesianFromPairMean_parameters]
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp (hW.preimage miuraCartesianFromPairMean.continuous) _ hbase
  obtain ⟨r,hr,hlift⟩ := Coeff.exists_ball_real_quadraticActions_lifts (q := 1)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) q₀ (miuraCartesianPairParameters_real z) (Metric.ball q₀ R)
      Metric.isOpen_ball (Metric.mem_ball_self hR)
  let V := N ⁻¹' Metric.ball (quadraticActionsExponent (q := 1) q₀) r ∩
    (fun b : MiuraActionMeanTarget => b.2) ⁻¹' Metric.ball z.val.2 R
  have hV : IsOpen V := (Metric.isOpen_ball.preimage N.continuous).inter
    (Metric.isOpen_ball.preimage continuous_snd)
  have hcenter : miuraPositiveCartesianActionMean z.val ∈ V := by
    refine ⟨?_,Metric.mem_ball_self hR⟩
    change N (miuraPositiveCartesianActionMean z.val) ∈ Metric.ball (quadraticActionsExponent (q := 1) q₀) r
    rw [miuraCartesianPairParameters_actions]
    exact Metric.mem_ball_self hr
  refine ⟨V,hV,hcenter,?_⟩
  intro b hb
  obtain ⟨q,⟨hq,hqr⟩,hquad⟩ := hlift ⟨hb.1,miuraCartesian_normalized_actions_nonnegative b⟩
  let v := miuraCartesianFromPairMean (q,(miuraPositiveCartesianActionMean b.val).2)
  have hvW : v ∈ W := by
    apply hball
    change max (dist q q₀) (dist (miuraPositiveCartesianActionMean b.val).2 z.val.2) < R
    exact max_lt hq hb.2
  refine ⟨v,hvW,miuraCartesianFromPairMean_real q hqr _ b.property.2,?_⟩
  exact miuraCartesianFromPairMean_action_of_quadratic_data q (miuraPositiveCartesianActionMean b.val)
    (miuraCartesian_actionMean_nonpositive b.val) hquad

end NLS.MKdV
