import NLS.ZakharovShabat.SourceFrequencyOriginalInverse
import NLS.ZakharovShabat.SourceStandardActionHamiltonian

/-! # Quadratic remainders in the original action-frequency expansion

The renormalized frequency has a quadratic sequence-norm remainder after
its linear term. Restoring mass and dispersion gives equation (4.3) for
the literal derivatives of the full Hamiltonian, uniformly over all indices.
-/
noncomputable section
open Set Filter Topology Asymptotics
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem analytic_linear_remainder
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (f : E → G) (hf : AnalyticAt ℂ f 0) :
    (fun a => f a - f 0 - fderiv ℂ f 0 a)
      =O[𝓝 0] (fun a => ‖a‖^2) := by
  obtain ⟨p,r,hp⟩ := hf
  have hrem := hp.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 2
  have hpoly (a : E) : p.partialSum 2 a = f 0 + fderiv ℂ f 0 a := by
    have h0 := hp.factorial_smul a 0
    have h1 := hp.factorial_smul a 1
    simp only [Nat.factorial_zero,one_smul,iteratedFDeriv_zero_apply] at h0
    simp only [Nat.factorial_one,one_smul,iteratedFDeriv_one_apply] at h1
    simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,h0,h1]
  apply hrem.congr_left
  intro a
  rw [zero_add,hpoly,sub_add_eq_sub_sub]

private theorem quadratic_bound_on_ball
    {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]
    (f : E → G) (U : Set E) (hU : U ∈ 𝓝 0)
    (h : f =O[𝓝 0] (fun a => ‖a‖^2)) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧ Metric.ball (0 : E) r ⊆ U ∧
      ∀ a : E, ‖a‖ < r → ‖f a‖ ≤ C*‖a‖^2 := by
  obtain ⟨C,hC,hb⟩ := h.exists_pos
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hb.bound)
  refine ⟨r,hr,C,hC,fun a ha => (hball ha).1,?_⟩
  intro a ha
  have h := (hball (by simpa only [Metric.mem_ball,dist_zero_right] using ha)).2
  simpa only [Set.mem_ofPred_eq,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using h

namespace SourceOriginalFrequencyData
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {U : Set (Coeff q)} {F : Coeff q → Coeff q}

/-- The full frequency-sequence error is quadratic in the original action norm. -/
theorem action_quadratic_remainder (E : SourceOriginalFrequencyData D U F) (hp2 : 2 < p) :
    (fun a : Coeff q => F a + (2 : ℂ) • a) =O[𝓝 0] (fun a => ‖a‖^2) := by
  have h := analytic_linear_remainder F (E.analytic 0 E.zero_mem)
  apply h.congr_left
  intro a
  rw [E.map_zero,E.derivative_zero hp2]
  change F a - 0 - ((-2 : ℂ) • a) = F a + (2 : ℂ) • a
  simp only [sub_zero,neg_smul,sub_neg_eq_add]

/-- A common domain ball and constant bound the entire remainder sequence. -/
theorem action_quadratic_remainder_bound (E : SourceOriginalFrequencyData D U F) (hp2 : 2 < p) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧ Metric.ball (0 : Coeff q) r ⊆ U ∧
      ∀ a : Coeff q, ‖a‖ < r → ‖F a + (2 : ℂ) • a‖ ≤ C*‖a‖^2 :=
  quadratic_bound_on_ball _ U (E.isOpen.mem_nhds E.zero_mem) (E.action_quadratic_remainder hp2)

end SourceOriginalFrequencyData
namespace SourceOriginalHamiltonianData
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4:ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- The Hilbert-valued error remains quadratic in the standard weighted action norm. -/
theorem standard_frequency_quadratic_remainder (Q : SourceOriginalHamiltonianData D T F H) :
    (fun a : WeightedCoeff (Weight.sobolev 2) 1 =>
      F (sourceStandardActionsToHilbert a) + (2 : ℂ) • sourceStandardActionsToHilbert a)
      =O[𝓝 0] (fun a => ‖a‖^2) := by
  let L := sourceStandardActionsToHilbert
  have ht : Tendsto L (𝓝 0) (𝓝 0) := by
    simpa only [L.map_zero] using L.continuous.continuousAt.tendsto (x := 0)
  have h := (Q.frequency.action_quadratic_remainder (by norm_num)).comp_tendsto ht
  have hb : (fun a => ‖L a‖^2) =O[𝓝 0] (fun a => ‖a‖^2) := by
    apply IsBigO.of_bound (‖L‖^2)
    filter_upwards [] with a
    simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    calc
      ‖L a‖^2 ≤ (‖L‖*‖a‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm a) 2
      _ = _ := mul_pow _ _ _
  exact h.trans hb

private theorem restore_frequency_linear_term (x m k a : ℂ) :
    x + 4*m + k = k + 4*m - 2*a + (x + 2*a) := by ring

private theorem standard_full_frequency_expansion_identity
    (Q : SourceOriginalHamiltonianData D T F H)
    (a : WeightedCoeff (Weight.sobolev 2) 1) (ha : sourceStandardActionsToHilbert a ∈ T) (n : ℤ) :
    deriv (fun z : ℂ => sourceStandardFullActionHamiltonian H
      (a + z • WeightedCoeff.single (Weight.sobolev 2) n 1)) 0 =
      (2*(Real.pi:ℂ)*n)^2 + 4*(∑' k : ℤ, a.val k) - 2*a.val n +
        (F (sourceStandardActionsToHilbert a)+(2:ℂ) • sourceStandardActionsToHilbert a) n := by
  rw [(Q.standard_full_action_coordinate_derivative a ha n).deriv]
  have hm : sourceStandardActionMass a = ∑' k : ℤ, a.val k := by
    simp only [sourceStandardActionMass,ContinuousLinearMap.comp_apply,
      sourceEnergyActionMass_eq_tsum,sourceStandardToEnergyActions_apply]
  have hn : sourceStandardActionsToHilbert a n = a.val n := by
    simp only [sourceStandardActionsToHilbert,ContinuousLinearMap.comp_apply,
      sourceEnergyActionsToHilbert_apply,sourceStandardToEnergyActions_apply]
  change F (sourceStandardActionsToHilbert a) n + 4*sourceStandardActionMass a + _ =
    _ + _ - _ + (F (sourceStandardActionsToHilbert a) n + 2*sourceStandardActionsToHilbert a n)
  rw [hm,hn]
  exact restore_frequency_linear_term _ _ _ _


private theorem comp_mem_preimage
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (L : X →L[ℂ] Y) (M : Y →L[ℂ] Z) (U : Set Z) (a : X)
    (ha : a ∈ L ⁻¹' (M ⁻¹' U)) : (M.comp L) a ∈ U := ha

private theorem standard_action_domain_mem
    (a : WeightedCoeff (Weight.sobolev 2) 1) (ha : a ∈ sourceStandardFullActionDomain T) :
    sourceStandardActionsToHilbert a ∈ T := by
  exact comp_mem_preimage sourceStandardToEnergyActions sourceEnergyActionsToHilbert T a ha

private theorem standard_frequency_remainder_bound (Q : SourceOriginalHamiltonianData D T F H) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      Metric.ball (0 : WeightedCoeff (Weight.sobolev 2) 1) r ⊆ sourceStandardFullActionDomain T ∧
      ∀ a : WeightedCoeff (Weight.sobolev 2) 1, ‖a‖ < r →
        ‖F (sourceStandardActionsToHilbert a)+(2:ℂ) • sourceStandardActionsToHilbert a‖ ≤ C*‖a‖^2 := by
  have h0 : (0 : WeightedCoeff (Weight.sobolev 2) 1) ∈ sourceStandardFullActionDomain T :=
    Q.standard_full_action_domain.2 (WeightedCoeff.zero_mem_nonnegativeLocus _ _)
  exact quadratic_bound_on_ball _ _
    (Q.standard_full_action_domain.1.mem_nhds h0) Q.standard_frequency_quadratic_remainder

/-- Equation (4.3) for literal full-Hamiltonian derivatives, with one quadratic
Hilbert remainder and one bound chosen before every signed spectral index. -/
theorem standard_full_frequency_expansion_bound (Q : SourceOriginalHamiltonianData D T F H) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      Metric.ball (0 : WeightedCoeff (Weight.sobolev 2) 1) r ⊆ sourceStandardFullActionDomain T ∧
      ∀ a : WeightedCoeff (Weight.sobolev 2) 1, ‖a‖ < r →
        ∃ R : Coeff 2, ‖R‖ ≤ C*‖a‖^2 ∧ ∀ n : ℤ,
          deriv (fun z : ℂ => sourceStandardFullActionHamiltonian H
            (a + z • WeightedCoeff.single (Weight.sobolev 2) n 1)) 0 =
            (2*(Real.pi:ℂ)*n)^2 + 4*(∑' k : ℤ, a.val k) - 2*a.val n + R n := by
  obtain ⟨r,hr,C,hC,hball,hbound⟩ := standard_frequency_remainder_bound Q
  refine ⟨r,hr,C,hC,hball,fun a ha =>
    ⟨F (sourceStandardActionsToHilbert a)+(2:ℂ) • sourceStandardActionsToHilbert a,hbound a ha,?_⟩⟩
  intro n
  have hmem := hball (mem_ball_zero_iff.mpr ha)
  exact standard_full_frequency_expansion_identity Q a (standard_action_domain_mem a hmem) n

end SourceOriginalHamiltonianData
end NLS.ZakharovShabat
