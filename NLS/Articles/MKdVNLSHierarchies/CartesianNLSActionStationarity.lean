import NLS.MKdV.MiuraNLSActionsCartesianStationarity

/-! # The full original NLS action sequence in physical Cartesian inverse coordinates

One open complex original L² source neighborhood maps onto a full open
native Cartesian/mean ball. On this ball the actual original signed NLS
actions form an analytic l1-valued map, recovering every original action
and stationary in every positive Cartesian rotation direction. Quotient
factorization through the quadratic radii and signed mean remains a
separate essential obligation.
-/
noncomputable section
open Set Metric Complex NLS.MKdV NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

theorem original_NLS_actions_cartesian_analytic_stationary_near_zero :
    ∃ U : Set (Coeff 2), ∃ R : ℝ, ∃ F : MiuraPositiveCartesianTarget → Coeff 1,
      IsOpen U ∧ (0 : Coeff 2) ∈ U ∧ 0 < R ∧
      miuraPositiveCartesianMap '' U = ball 0 R ∧ AnalyticOnNhd ℂ F (ball 0 R) ∧
      (∀ a ∈ U, ∀ k : ℤ, F (miuraPositiveCartesianMap a) k =
        sourceComplexAction (by simp) (by norm_num) k (scalarL2Diagonal a)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ z ∈ ball 0 R,
        fderiv ℂ F z (miuraCartesianActionVector n z) = 0) := by
  obtain ⟨C⟩ := nonempty_miuraCartesianNLSActionChart
  refine ⟨C.source,C.radius,C.observables,C.source_open,C.source_zero,C.radius_pos,C.image_source,C.observables_analytic,?_,?_⟩
  · intro a ha k
    have hMa : miuraPositiveCartesianMap a ∈ ball 0 C.radius := by
      rw [← C.image_source]
      exact ⟨a,ha,rfl⟩
    have hdom := C.inverse_action_domain _ hMa
    rw [C.left_inverse a ha] at hdom
    rw [C.observables_recover a ha]
    exact miuraOriginalNLSActionSequence_apply a hdom k
  · exact C.observables_rotation_stationary

end NLS.Articles.MKdVNLSHierarchies
