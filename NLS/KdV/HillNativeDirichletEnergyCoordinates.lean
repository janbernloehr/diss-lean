import NLS.KdV.HillNativeDirichletEnergyRemainder
import NLS.SequenceSpaces.PositiveDeletedProjectionBounds

/-! # Native mean-subtracted Dirichlet energy coordinates and their derivative -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

def hillDirichletEnergyLinearPart : Coeff 2 →L[ℂ] Coeff 2 :=
  (-1/2 : ℂ) • ((Coeff.positiveDeletedProjection 2 0).comp
    (ContinuousLinearMap.id ℂ (Coeff 2)+(Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap))

theorem hillDirichletEnergyLinearPart_apply (u : Coeff 2) (j : ℤ) :
    hillDirichletEnergyLinearPart u j = if 0 < j then -(u j+u (-j))/2 else 0 := by
  change (-1/2 : ℂ)*(Coeff.positiveDeletedProjection 2 0 (u+Coeff.reflection u)) j = _
  rw [Coeff.positiveDeletedProjection_apply]
  by_cases hj : 0 < j
  · rw [if_pos ⟨hj,ne_of_gt hj⟩,if_pos hj,lp.coeFn_add,Pi.add_apply,Coeff.reflection_apply]
    ring
  · rw [if_neg (by omega : ¬ (0 < j ∧ j ≠ 0)),if_neg hj,mul_zero]

theorem norm_hillDirichletEnergyLinearPart_le (u : Coeff 2) :
    ‖hillDirichletEnergyLinearPart u‖ ≤ ‖u‖ := by
  change ‖(-1/2 : ℂ) • Coeff.positiveDeletedProjection 2 0 (u+Coeff.reflection u)‖ ≤ _
  rw [norm_smul,norm_div,norm_neg,norm_one,norm_ofNat]
  have h := (Coeff.norm_positiveDeletedProjection_le 0 (u+Coeff.reflection u)).trans
    (norm_add_le u (Coeff.reflection u))
  rw [Coeff.reflection.norm_map] at h
  nlinarith

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeDirichletEnergyDeviations (u : Coeff 2) : Coeff 2 :=
  hillNativeDirichletEnergyRemainder h0q h0r u+hillDirichletEnergyLinearPart u

theorem exists_hillNativeDirichletEnergyDeviations_analytic_bound :
    ∃ η K : ℝ, 0 < η ∧ 0 < K ∧
      AnalyticOnNhd ℂ (hillNativeDirichletEnergyDeviations h0q h0r) (ball (0 : Coeff 2) η) ∧
      hillNativeDirichletEnergyDeviations h0q h0r 0 = 0 ∧
      HasFDerivAt (hillNativeDirichletEnergyDeviations h0q h0r) hillDirichletEnergyLinearPart 0 ∧
      ∀ u ∈ ball (0 : Coeff 2) η,
        ‖hillNativeDirichletEnergyDeviations h0q h0r u‖ ≤ ‖u‖+K*‖u‖^2 ∧
        ‖hillNativeDirichletEnergyDeviations h0q h0r u-hillDirichletEnergyLinearPart u‖ ≤ K*‖u‖^2 ∧
        (∀ k : ℕ+, hillNativeDirichletEnergyDeviations h0q h0r u (k : ℤ) =
          hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)-freeHillEnergy k-u 0) ∧
        ∀ j : ℤ, j ≤ 0 → hillNativeDirichletEnergyDeviations h0q h0r u j = 0 := by
  obtain ⟨η,K,hη,hK,hRa,hR0,hDR,hR⟩ := exists_hillNativeDirichletEnergyRemainder_analytic_bound h0q h0r
  refine ⟨η,K,hη,hK,?_,?_,?_,?_⟩
  · exact fun u hu => (hRa u hu).add (hillDirichletEnergyLinearPart.analyticAt u)
  · change hillNativeDirichletEnergyRemainder h0q h0r 0+hillDirichletEnergyLinearPart 0 = 0
    rw [hR0,map_zero,add_zero]
  · have h := hDR.add hillDirichletEnergyLinearPart.hasFDerivAt
    rw [zero_add] at h
    convert! h using 1
  · intro u hu
    have hnorm := (hR u hu).1
    refine ⟨?_,?_,?_,?_⟩
    · exact (norm_add_le _ _).trans ((add_le_add hnorm (norm_hillDirichletEnergyLinearPart_le u)).trans_eq (by ring))
    · change ‖hillNativeDirichletEnergyRemainder h0q h0r u+hillDirichletEnergyLinearPart u-hillDirichletEnergyLinearPart u‖ ≤ _
      rwa [add_sub_cancel_right]
    · intro k
      have hk : (0 : ℤ) < k := by exact_mod_cast k.pos
      change (hillNativeDirichletEnergyRemainder h0q h0r u+hillDirichletEnergyLinearPart u) (k : ℤ) = _
      rw [lp.coeFn_add,Pi.add_apply,(hR u hu).2.1 k,hillDirichletEnergyLinearPart_apply,if_pos hk]
      ring
    · intro j hj
      change (hillNativeDirichletEnergyRemainder h0q h0r u+hillDirichletEnergyLinearPart u) j = _
      rw [lp.coeFn_add,Pi.add_apply,(hR u hu).2.2 j hj,hillDirichletEnergyLinearPart_apply,
        if_neg (by omega : ¬ 0 < j),add_zero]

end NLS.KdV
