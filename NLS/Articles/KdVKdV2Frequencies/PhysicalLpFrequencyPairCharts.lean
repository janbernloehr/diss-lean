import NLS.KdV.PhysicalMiuraLpFrequencyChart
import NLS.Articles.KdVConvexity.PhysicalFrequencyPairInvariance
import NLS.KdV.ClassicalPeriodOperator
import NLS.Articles.KdVKdV2Frequencies.GlobalWeakFrequencyNormalization

/-! The SAME actual global weak inverse has local physical pair charts
whose frequency corrections divided by n form genuine ellr packets,
including at every real rough source and every closed-action boundary. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

structure PhysicalLpFrequencyPairChart (D : GlobalRoughAbelianForwardData)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] where
  physical : PhysicalFrequencyPairChart D
  packet : (Coeff 2 × Coeff 2) → Coeff r
  analytic_packet : AnalyticOnNhd ℂ packet physical.domain
  bound : ℝ
  bound_pos : 0<bound
  norm_packet : ∀ z∈physical.domain, ‖packet z‖≤bound
  nonpositive : ∀ z∈physical.domain, ∀ j : ℤ, j≤0 → packet z j=0
  positive : ∀ z∈physical.domain, ∀ n : ℕ+, packet z (n : ℤ)=physical.correction n z/(n : ℂ)

theorem exists_physicalLpFrequencyPairChart (D : GlobalRoughAbelianForwardData)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1<r) (q : PeriodOneHminusOne)
    (hqr : IsRealPeriodOneHminusOne q) (hqm : q.val 0=0) :
    ∃ P : PhysicalLpFrequencyPairChart D r, ∃ z : Coeff 2 × Coeff 2,
      z∈P.physical.domain ∧ z∈Coeff.realPairLocus 2 ∧ P.physical.potential z=q := by
  obtain ⟨z,hzr,U,hU,hzU,Q,hQ,hQz,hd⟩ := exists_hillRough_pair_inverse D actionIndexEquiv q hqr hqm
  obtain ⟨B,hqB,_⟩ := exists_physicalMiuraLpFrequencyChart hr q hqr 0
  let V := U∩Q ⁻¹' B.physical.domain
  let P : PhysicalFrequencyPairChart D :=
    ⟨V,hQ.continuousOn.isOpen_inter_preimage hU B.physical.domain_open,Q,hQ.mono inter_subset_left,
      (fun w hw => (hd w hw.1).1),(fun w hw => (hd w hw.1).2.1),
      (fun w hw hwr => (hd w hw.1).2.2 hwr),B.physical,(fun w hw => hw.2)⟩
  refine ⟨⟨P,(fun w => B.packet (Q w)),
    (fun w hw => (B.analytic_packet _ hw.2).comp (hQ w hw.1)),B.bound,B.bound_pos,
    (fun w hw => B.norm_packet _ hw.2),(fun w hw => B.nonpositive _ hw.2),
    (fun w hw => B.positive _ hw.2)⟩,z,⟨hzU,?_⟩,hzr,hQz⟩
  change Q z∈B.physical.domain
  rwa [hQz]

theorem exists_physicalLp_pair_of_nonnegative_actions (D : GlobalRoughAbelianForwardData)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1<r) (b : Coeff 1) (hb : b∈Coeff.nonnegativeLocus 1) :
    ∃ P : PhysicalLpFrequencyPairChart D r, ∃ z : Coeff 2 × Coeff 2,
      z∈P.physical.domain ∧ z∈Coeff.realPairLocus 2 ∧ quadraticActionsExponent (q := 1) z=b := by
  obtain ⟨Ω,I,_hΩ,hΩr,hI,hrec,_hpos,_hsurj⟩ := exists_global_analytic_Arnold_map_onto_cone
  have hbp : baseActionNormalization.symm b∈WeightedCoeff.nonnegativeLocus baseActionWeight 1 := by
    apply (WeightedCoeff.mem_nonnegativeLocus_iff baseActionWeight 1 _).mpr
    change baseActionNormalization (baseActionNormalization.symm b)∈Coeff.nonnegativeLocus 1
    rwa [baseActionNormalization.apply_symm_apply]
  obtain ⟨q,hqr,hqm,hqI⟩ := exists_source_of_nonnegative_Arnold_actions Ω hΩr I hI hrec
    (baseActionNormalization.symm b) hbp
  obtain ⟨P,z,hz,hzr,hzq⟩ := exists_physicalLpFrequencyPairChart D hr q hqr hqm
  refine ⟨P,z,hz,hzr,?_⟩
  have he := Arnold_action_of_pair_inverse_identity D Ω hΩr I hI hrec
    (P.physical.potential z) (P.physical.real_potential z hz hzr) z hzr (P.physical.signed_inverse z hz)
  rw [hzq,hqI] at he
  have hh := congrArg baseActionNormalization he
  rw [baseActionNormalization.apply_symm_apply] at hh
  exact (WeightedCoeff.weight_actionsFromNormalizedCoordinates baseActionWeight z).symm.trans hh.symm

namespace PhysicalLpFrequencyPairChart
variable {D : GlobalRoughAbelianForwardData} {r : ℝ≥0∞} [Fact (1 ≤ r)]

theorem packet_eq_of_real_actions (P Q : PhysicalLpFrequencyPairChart D r)
    (z : Coeff 2 × Coeff 2) (hz : z∈P.physical.domain)
    (w : Coeff 2 × Coeff 2) (hw : w∈Q.physical.domain)
    (hzr : z∈Coeff.realPairLocus 2) (hwr : w∈Coeff.realPairLocus 2)
    (ha : quadraticActionsExponent (q := 1) w=quadraticActionsExponent z) : P.packet z=Q.packet w := by
  ext j
  by_cases hj : 0<j
  · let n := positiveIntegerIndex j hj
    have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
    rw [←hnj,P.positive z hz n,Q.positive w hw n,
      P.physical.correction_eq_of_real_actions Q.physical z hz w hw hzr hwr ha n]
  · rw [P.nonpositive z hz j (by omega),Q.nonpositive w hw j (by omega)]

end PhysicalLpFrequencyPairChart
end NLS.Articles.KdVKdV2Frequencies
