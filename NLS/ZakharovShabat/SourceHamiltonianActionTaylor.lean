import NLS.ZakharovShabat.SourceStandardActionHamiltonian
import NLS.ZakharovShabat.SourceHamiltonianOriginalNonextension

/-! # The action Hamiltonian expansion with a cubic remainder

The actual renormalized Hamiltonian has quadratic term minus the full
bilinear square sum. Restoring mass and kinetic energy gives the printed
full expansion in the standard weighted action norm.
-/
noncomputable section
open Set Filter Topology Asymptotics
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem analytic_quadratic_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (hf : AnalyticAt ℂ f 0) :
    (fun a => f a - f 0 - fderiv ℂ f 0 a -
      (1/2:ℂ) * fderiv ℂ (fderiv ℂ f) 0 a a)
      =O[𝓝 0] (fun a => ‖a‖^3) := by
  obtain ⟨p,r,hp⟩ := hf
  have hrem := hp.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 3
  have hpoly (a : E) : p.partialSum 3 a =
      f 0 + fderiv ℂ f 0 a + (1/2:ℂ)*fderiv ℂ (fderiv ℂ f) 0 a a := by
    have h0 := hp.factorial_smul a 0
    have h1 := hp.factorial_smul a 1
    have h2 := hp.factorial_smul a 2
    simp only [Nat.factorial_zero,one_smul,iteratedFDeriv_zero_apply] at h0
    simp only [Nat.factorial_one,one_smul,iteratedFDeriv_one_apply] at h1
    simp only [Nat.factorial_two,iteratedFDeriv_two_apply,two_smul] at h2
    simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,h0,h1]
    linear_combination h2 / 2
  apply hrem.congr_left
  intro a
  rw [zero_add,hpoly]
  ring

private theorem cubic_bound_on_ball
    {E : Type*} [NormedAddCommGroup E] (f : E → ℂ) (U : Set E)
    (hU : U ∈ 𝓝 0) (h : f =O[𝓝 0] (fun a => ‖a‖^3)) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧ Metric.ball (0 : E) r ⊆ U ∧
      ∀ a : E, ‖a‖ < r → ‖f a‖ ≤ C*‖a‖^3 := by
  obtain ⟨C,hC,hb⟩ := h.exists_pos
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hb.bound)
  refine ⟨r,hr,C,hC,fun a ha => (hball ha).1,?_⟩
  intro a ha
  have h := (hball (by simpa only [Metric.mem_ball,dist_zero_right] using ha)).2
  simpa only [Set.mem_ofPred_eq,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using h

namespace SourceOriginalHamiltonianData
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4:ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- The actual Hilbert action Hamiltonian has its full quadratic term,
with a uniform cubic remainder near zero, including infinite-support inputs. -/
theorem action_cubic_remainder (Q : SourceOriginalHamiltonianData D T F H) :
    (fun a : Coeff 2 => H a + Coeff.dualPairing a a)
      =O[𝓝 0] (fun a => ‖a‖^3) := by
  have h := analytic_quadratic_remainder H (Q.analytic 0 Q.frequency.zero_mem)
  convert h using 1
  funext a
  rw [Q.map_zero,Coeff.fderiv_eq_dualPairing_scalarGradient,Q.gradient_zero,
    Q.hessian_zero]
  simp only [_root_.map_zero,zero_apply]
  ring

/-- Section 18's full expansion, with the omitted higher-order terms
bounded by the cube of the standard ell^(2,1) action norm. -/
theorem standard_full_action_cubic_remainder (Q : SourceOriginalHamiltonianData D T F H) :
    (fun a : WeightedCoeff (Weight.sobolev 2) 1 =>
      sourceStandardFullActionHamiltonian H a -
        ((∑' n : ℤ, (2*(Real.pi:ℂ)*n)^2*a.val n) +
          2*(∑' n : ℤ, a.val n)^2 - ∑' n : ℤ, (a.val n)^2))
      =O[𝓝 0] (fun a => ‖a‖^3) := by
  let L := sourceStandardActionsToHilbert
  have ht : Tendsto L (𝓝 0) (𝓝 0) := by
    simpa only [_root_.map_zero] using L.continuous.continuousAt.tendsto (x := 0)
  have h := Q.action_cubic_remainder.comp_tendsto ht
  have hb : (fun a => ‖L a‖^3) =O[𝓝 0] (fun a => ‖a‖^3) := by
    apply IsBigO.of_bound (‖L‖^3)
    filter_upwards [] with a
    simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    calc
      ‖L a‖^3 ≤ (‖L‖*‖a‖)^3 := pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm a) 3
      _ = _ := mul_pow _ _ _
  apply (h.trans hb).congr_left
  intro a
  simp only [Function.comp_apply]
  rw [sourceStandardFullActionHamiltonian_eq,Coeff.dualPairing_apply]
  have he : (∑' n : ℤ, L a n * L a n) = ∑' n : ℤ, (a.val n)^2 := by
    apply tsum_congr
    intro n
    simp only [L,sourceStandardActionsToHilbert,ContinuousLinearMap.comp_apply,
      sourceEnergyActionsToHilbert_apply,sourceStandardToEnergyActions_apply,pow_two]
  rw [he]
  dsimp only [L,sourceStandardActionsToHilbert,ContinuousLinearMap.comp_apply]
  ring

/-- One ball in the original standard weighted action domain and one
constant bound the full expansion's remainder for every input on that ball. -/
theorem standard_full_action_expansion_bound (Q : SourceOriginalHamiltonianData D T F H) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      Metric.ball (0 : WeightedCoeff (Weight.sobolev 2) 1) r ⊆ sourceStandardFullActionDomain T ∧
      ∀ a : WeightedCoeff (Weight.sobolev 2) 1, ‖a‖ < r →
        ‖sourceStandardFullActionHamiltonian H a -
          ((∑' n : ℤ, (2*(Real.pi:ℂ)*n)^2*a.val n) +
            2*(∑' n : ℤ, a.val n)^2 - ∑' n : ℤ, (a.val n)^2)‖ ≤ C*‖a‖^3 := by
  have h0 : (0 : WeightedCoeff (Weight.sobolev 2) 1) ∈ sourceStandardFullActionDomain T :=
    Q.standard_full_action_domain.2 (WeightedCoeff.zero_mem_nonnegativeLocus _ _)
  exact cubic_bound_on_ball _ _ (Q.standard_full_action_domain.1.mem_nhds h0)
    Q.standard_full_action_cubic_remainder

end SourceOriginalHamiltonianData
end NLS.ZakharovShabat
