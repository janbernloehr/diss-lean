import NLS.KdV.HillNativeGapMidpointRemainder
import NLS.KdV.HillNativeDirichletEnergyCoordinates

/-! # The actual Dirichlet displacement from the symmetric midpoint in Hilbert norm -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeDirichletMidpointDisplacements (u : Coeff 2) : Coeff 2 :=
  hillNativeDirichletEnergyDeviations h0q h0r u-hillNativeGapMidpointRemainder h0q h0r u

theorem exists_hillNativeDirichletMidpointDisplacements_analytic_bound :
    ∃ η K : ℝ, 0 < η ∧ 0 < K ∧
      AnalyticOnNhd ℂ (hillNativeDirichletMidpointDisplacements h0q h0r) (ball (0 : Coeff 2) η) ∧
      hillNativeDirichletMidpointDisplacements h0q h0r 0 = 0 ∧
      HasFDerivAt (hillNativeDirichletMidpointDisplacements h0q h0r) hillDirichletEnergyLinearPart 0 ∧
      ∀ u ∈ ball (0 : Coeff 2) η,
        ‖hillNativeDirichletMidpointDisplacements h0q h0r u‖ ≤ ‖u‖+K*‖u‖^2 ∧
        ‖hillNativeDirichletMidpointDisplacements h0q h0r u-hillDirichletEnergyLinearPart u‖ ≤ K*‖u‖^2 ∧
        (∀ k : ℕ+, hillNativeDirichletMidpointDisplacements h0q h0r u (k : ℤ) =
          hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)-
            hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)) ∧
        ∀ j : ℤ, j ≤ 0 → hillNativeDirichletMidpointDisplacements h0q h0r u j = 0 := by
  obtain ⟨ηd,Kd,hηd,hKd,hDa,hD0,hDD,hD⟩ := exists_hillNativeDirichletEnergyDeviations_analytic_bound h0q h0r
  obtain ⟨ηr,Kr,hηr,hKr,hRa,hR0,hDR,hR⟩ := exists_hillNativeGapMidpointRemainder_analytic_bound h0q h0r
  let η := min ηd ηr
  have hd : ball (0 : Coeff 2) η ⊆ ball 0 ηd := ball_subset_ball (min_le_left _ _)
  have hr : ball (0 : Coeff 2) η ⊆ ball 0 ηr := ball_subset_ball (min_le_right _ _)
  refine ⟨η,Kd+Kr,lt_min hηd hηr,add_pos hKd hKr,?_,?_,?_,?_⟩
  · exact fun u hu => (hDa u (hd hu)).sub (hRa u (hr hu))
  · change hillNativeDirichletEnergyDeviations h0q h0r 0-hillNativeGapMidpointRemainder h0q h0r 0 = 0
    rw [hD0,hR0,sub_self]
  · have h := hDD.sub hDR
    rw [sub_zero] at h
    convert! h using 1
  · intro u hu
    have hnormD := (hD u (hd hu)).1
    have hnormR := (hR u (hr hu)).1
    refine ⟨?_,?_,?_,?_⟩
    · exact (norm_sub_le _ _).trans ((add_le_add hnormD hnormR).trans_eq (by ring))
    · change ‖hillNativeDirichletEnergyDeviations h0q h0r u-hillNativeGapMidpointRemainder h0q h0r u-
        hillDirichletEnergyLinearPart u‖ ≤ _
      rw [sub_right_comm]
      exact (norm_sub_le _ _).trans ((add_le_add (hD u (hd hu)).2.1 hnormR).trans_eq (by ring))
    · intro k
      change (hillNativeDirichletEnergyDeviations h0q h0r u-hillNativeGapMidpointRemainder h0q h0r u) (k : ℤ) = _
      rw [lp.coeFn_sub,Pi.sub_apply,(hD u (hd hu)).2.2.1 k,(hR u (hr hu)).2.1 k]
      ring
    · intro j hj
      change (hillNativeDirichletEnergyDeviations h0q h0r u-hillNativeGapMidpointRemainder h0q h0r u) j = _
      rw [lp.coeFn_sub,Pi.sub_apply,(hD u (hd hu)).2.2.2 j hj,(hR u (hr hu)).2.2 j hj,sub_self]

end NLS.KdV
