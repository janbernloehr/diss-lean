import NLS.Articles.KdVKdV2Frequencies.GlobalLpFrequencyActionCharts

/-! Genuine Banach-analytic finite-exponent packets of the ACTUAL physical
KdV correction divided by n on a complex neighborhood of the ENTIRE weak
cone. Every native source is recovered with no smallness premise. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem lp_packet_recovers_all_physical_pairs (D : GlobalRoughAbelianForwardData)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1<r) (G : Coeff 1 → Coeff r)
    (hrec : ∀ (P : PhysicalLpFrequencyPairChart D r) (z : Coeff 2 × Coeff 2),
      z∈P.physical.domain → z∈Coeff.realPairLocus 2 → G (quadraticActionsExponent (q := 1) z)=P.packet z)
    (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2)
    (hz : z∈P.domain) (hzr : z∈Coeff.realPairLocus 2) (n : ℕ+) :
    G (quadraticActionsExponent (q := 1) z) (n : ℤ)=P.correction n z/(n : ℂ) := by
  obtain ⟨Q,w,hw,hwr,hQ⟩ := exists_physicalLp_pair_of_nonnegative_actions D hr
    (quadraticActionsExponent (q := 1) z) (Coeff.quadraticActions_mem_nonnegativeLocus z hzr)
  have he := congrArg (fun b : Coeff r => b (n : ℤ)) (hrec Q w hw hwr)
  rw [hQ] at he
  rw [he,Q.positive w hw n,
    Q.physical.correction_eq_of_real_actions P w hw z hz hwr hzr hQ.symm n]

theorem lp_packet_native_recovery (D : GlobalRoughAbelianForwardData)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1<r) (G : Coeff 1 → Coeff r)
    (hrec : ∀ (P : PhysicalLpFrequencyPairChart D r) (z : Coeff 2 × Coeff 2),
      z∈P.physical.domain → z∈Coeff.realPairLocus 2 → G (quadraticActionsExponent (q := 1) z)=P.packet z)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) (n : ℕ+) :
    G (weakActionEnumeration (D.nativeWeakActionSequence 1 q)) (n : ℤ)=
      ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)/(n : ℂ) := by
  let F : ℕ+ → Coeff 1 → ℂ := fun n b => (n : ℂ)*G b (n : ℤ)
  have hF (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2)
      (hz : z∈P.domain) (hzr : z∈Coeff.realPairLocus 2) (n : ℕ+) :
      F n (quadraticActionsExponent (q := 1) z)=P.correction n z := by
    change (n : ℂ)*G (quadraticActionsExponent (q := 1) z) (n : ℤ)=_
    rw [lp_packet_recovers_all_physical_pairs D hr G hrec P z hz hzr n]
    have hn : (n : ℂ)≠0 := by exact_mod_cast n.pos.ne'
    field_simp
  have he := global_physical_family_native_recovery D F hF q n
  have hn : (n : ℂ)≠0 := by exact_mod_cast n.pos.ne'
  exact (eq_div_iff hn).mpr ((mul_comm _ _).trans he)

namespace GlobalRoughAbelianForwardData

theorem exists_global_actual_weak_lp_kdv_frequency_packet (D : GlobalRoughAbelianForwardData)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1<r) :
    ∃ U : Set (Coeff 1), ∃ g : Coeff 1 → Coeff r,
      IsOpen U ∧ Coeff.nonnegativeLocus 1⊆U ∧ AnalyticOnNhd ℂ g U ∧
      (∀ a∈U, ∀ j : ℤ, j≤0 → g a j=0) ∧
      (∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, (g a j).im=0) ∧
      (∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
        z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n : ℕ+,
          g ((positiveOneExtendIsometry actionIndexEquiv) (quadraticActionsExponent (q := 1) z)) (n : ℤ)=
            P.correction n z/(n : ℂ)) ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)), ∀ n : ℕ+,
        g (D.nativeWeakActionSequence 1 q) (n : ℤ)=
          ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)/(n : ℂ) := by
  obtain ⟨V,G,hV,hcone,hG,hzero,hrec⟩ := exists_global_physical_lp_action_packet D hr
  let U := weakActionEnumeration ⁻¹' V
  let g := fun a => G (weakActionEnumeration a)
  have hU : IsOpen U := hV.preimage weakActionEnumeration.continuous
  have hconeU : Coeff.nonnegativeLocus 1⊆U := fun a ha => hcone (weakActionEnumeration_nonnegative a ha)
  have hga : AnalyticOnNhd ℂ g U := fun a ha => (hG _ ha).comp (weakActionEnumeration.analyticAt a)
  refine ⟨U,g,hU,hconeU,hga,(fun a ha => hzero _ ha),?_,?_,?_⟩
  · intro a ha j
    by_cases hj : 0<j
    · let n := positiveIntegerIndex j hj
      have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
      obtain ⟨P,z,hz,hzr,hQ⟩ := exists_physical_pair_of_nonnegative_actions D (weakActionEnumeration a)
        (weakActionEnumeration_nonnegative a ha)
      change (G (weakActionEnumeration a) j).im=0
      rw [←hnj,←hQ,lp_packet_recovers_all_physical_pairs D hr G hrec P z hz hzr n]
      have hi : (P.correction n z).im=0 := physicalMiuraFrequencyChart_real D P.source_chart
        (P.potential z) (P.real_potential z hz hzr) (P.mean_zero z hz) (P.source_mem z hz) n
      simp only [div_im,Complex.natCast_re,Complex.natCast_im,hi,mul_zero,zero_mul,sub_zero,zero_div]
    · change (G (weakActionEnumeration a) j).im=0
      rw [hzero _ (hconeU ha) j (by omega)];rfl
  · intro P z hz hzr n
    change G (weakActionEnumeration ((positiveOneExtendIsometry actionIndexEquiv) (quadraticActionsExponent z))) (n : ℤ)=_
    have he (b : Coeff 1) : weakActionEnumeration ((positiveOneExtendIsometry actionIndexEquiv) b)=b := by
      ext k
      rw [weakActionEnumeration_apply]
      exact positiveOneExtendFunction_index actionIndexEquiv b k
    rw [he]
    exact lp_packet_recovers_all_physical_pairs D hr G hrec P z hz hzr n
  · intro q n
    exact lp_packet_native_recovery D hr G hrec q n

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
