import NLS.ZakharovShabat.SourcePhysicalFrequencyAsymptotic
import NLS.SequenceSpaces.ActionMassNonextension

/-! # Ordinary action frequencies do not extend continuously above ell1

The literal coordinate derivative of the full physical action Hamiltonian
contains the renormalized frequency, four times total action, and free
dispersion. Native weighted unit-mass blocks tend to zero in every action
exponent q>1, while their ordinary frequency retains the mass shift four.
This rules out continuous local extensions, even relative to the nonnegative
cone. The proof uses the actual energy derivative for the retained H.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Unit-mass blocks in the native full-energy action space. -/
def sourceEnergyMassBlock (N : ℕ) : SourceEnergyActions :=
  (((((N+1:ℕ):ℝ)⁻¹):ℝ):ℂ) •
    ∑ k ∈ Finset.range (N+1), WeightedCoeff.single sourceEnergyActionWeight.toWeight (k:ℤ) 1

theorem sourceEnergyMassBlock_hilbert (N : ℕ) :
    sourceEnergyActionsToHilbert (sourceEnergyMassBlock N) = Coeff.positiveMassBlock 2 N := by
  simp only [sourceEnergyMassBlock,map_smul,map_sum,sourceEnergyActionsToHilbert_single,
    Coeff.positiveMassBlock,Coeff.positiveUnitBlock]

theorem sourceEnergyMassBlock_mass (N : ℕ) : sourceEnergyActionMass (sourceEnergyMassBlock N) = 1 := by
  rw [sourceEnergyActionMass_eq_tsum]
  have he (n : ℤ) : (sourceEnergyMassBlock N).val n = Coeff.positiveMassBlock 1 N n := by
    have h := congrArg (fun a : Coeff 2 => a n) (sourceEnergyMassBlock_hilbert N)
    simpa only [sourceEnergyActionsToHilbert_apply,Coeff.positiveMassBlock,
      Coeff.positiveUnitBlock,lp.coeFn_smul,Pi.smul_apply,lp.coeFn_sum,
      Finset.sum_apply,lp.single_apply] using h
  simp_rw [he]
  exact Coeff.tsum_positiveMassBlock N

theorem sourceEnergyMassBlock_nonnegative (N : ℕ) :
    sourceEnergyMassBlock N ∈ WeightedCoeff.nonnegativeLocus sourceEnergyActionWeight.toWeight 1 := by
  intro n
  have h := congrArg (fun a : Coeff 2 => a n) (sourceEnergyMassBlock_hilbert N)
  change ((sourceEnergyMassBlock N).val n).im = 0 ∧ 0 ≤ ((sourceEnergyMassBlock N).val n).re
  rw [← sourceEnergyActionsToHilbert_apply,h]
  exact Coeff.positiveMassBlock_mem_nonnegativeLocus 2 N n

/-- The same native energy actions in any larger action exponent. -/
def sourceEnergyActionsToExponent (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    SourceEnergyActions →L[ℂ] Coeff q :=
  (Coeff.exponentInclusion (Fact.out : 1 ≤ q)).comp sourceEnergyActionsToSummable

@[simp] theorem sourceEnergyActionsToExponent_apply (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (a : SourceEnergyActions) (n : ℤ) : sourceEnergyActionsToExponent q a n = a.val n :=
  sourceEnergyActionsToSummable_apply a n

theorem sourceEnergyMassBlock_exponent (q : ℝ≥0∞) [Fact (1 ≤ q)] (N : ℕ) :
    sourceEnergyActionsToExponent q (sourceEnergyMassBlock N) = Coeff.positiveMassBlock q N := by
  have hs : sourceEnergyActionsToSummable (sourceEnergyMassBlock N) = Coeff.positiveMassBlock 1 N := by
    ext n
    have he := congrArg (fun a : Coeff 2 => a n) (sourceEnergyMassBlock_hilbert N)
    simpa only [sourceEnergyActionsToSummable_apply,sourceEnergyActionsToHilbert_apply,
      Coeff.positiveMassBlock,Coeff.positiveUnitBlock,lp.coeFn_smul,Pi.smul_apply,
      lp.coeFn_sum,Finset.sum_apply,lp.single_apply] using he
  change Coeff.exponentInclusion (Fact.out : 1 ≤ q)
    (sourceEnergyActionsToSummable (sourceEnergyMassBlock N)) = _
  rw [hs,Coeff.positiveMassBlock_exponent]

/-- Unit-mass native actions converge to zero in each larger action norm. -/
theorem sourceEnergyMassBlock_tendsto (q : ℝ≥0∞) [Fact (1 ≤ q)] (h1q : 1 < q) :
    Tendsto (fun N => sourceEnergyActionsToExponent q (sourceEnergyMassBlock N)) atTop (𝓝 0) := by
  simp_rw [sourceEnergyMassBlock_exponent]
  exact Coeff.tendsto_positiveMassBlock h1q

namespace SourceOriginalHamiltonianData
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4:ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

theorem full_action_frequency_zero_value (Q : SourceOriginalHamiltonianData D T F H) (n : ℤ) :
    sourceFullActionFrequency H 0 n = (2*(Real.pi:ℂ)*n)^2 := by
  rw [Q.full_action_frequency_eq 0 (by simpa only [map_zero] using Q.frequency.zero_mem) n]
  simp only [map_zero,Q.frequency.map_zero,lp.coeFn_zero,Pi.zero_apply,mul_zero,zero_add]

theorem energyMassBlock_mem (Q : SourceOriginalHamiltonianData D T F H) (N : ℕ) :
    Coeff.positiveMassBlock 2 N ∈ T := by
  let a := Coeff.positiveMassBlock 1 N
  have ha := Coeff.positiveMassBlock_mem_nonnegativeLocus 1 N
  have hre : RealCoeff.complexCLM 1 (Coeff.reCLM 1 a) = a :=
    RealCoeff.complexCLM_reCLM 1 a (fun n => (ha n).1)
  have h := Q.frequency.positive_actions_mem (Coeff.reCLM 1 a) (fun n => (ha n).2)
  rw [hre] at h
  exact (Coeff.positiveMassBlock_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2) N) ▸ h

theorem full_action_frequency_energyMassBlock
    (Q : SourceOriginalHamiltonianData D T F H) (n : ℤ) (N : ℕ) :
    sourceFullActionFrequency H (sourceEnergyMassBlock N) n =
      F (Coeff.positiveMassBlock 2 N) n + 4 + (2*(Real.pi:ℂ)*n)^2 := by
  have hm : sourceEnergyActionsToHilbert (sourceEnergyMassBlock N) ∈ T := by
    rw [sourceEnergyMassBlock_hilbert]
    exact Q.energyMassBlock_mem N
  calc
    sourceFullActionFrequency H (sourceEnergyMassBlock N) n =
        F (sourceEnergyActionsToHilbert (sourceEnergyMassBlock N)) n +
          4 * sourceEnergyActionMass (sourceEnergyMassBlock N) + (2*(Real.pi:ℂ)*n)^2 :=
      Q.full_action_frequency_eq (sourceEnergyMassBlock N) hm n
    _ = _ := by rw [sourceEnergyMassBlock_hilbert,sourceEnergyMassBlock_mass,mul_one]

/-- Along the native unit-mass blocks the full frequency retains the exact
mass shift four, although their larger-exponent action norms tend to zero. -/
theorem full_action_frequency_energyMassBlock_limit
    (Q : SourceOriginalHamiltonianData D T F H) (n : ℤ) :
    Tendsto (fun N => sourceFullActionFrequency H (sourceEnergyMassBlock N) n) atTop
      (𝓝 (4+(2*(Real.pi:ℂ)*n)^2)) := by
  have hF : ContinuousAt (fun b : Coeff 2 => F b n) 0 :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.continuousAt.comp
      (Q.frequency.analytic 0 Q.frequency.zero_mem).continuousAt
  have ht := ((hF.tendsto.comp (Coeff.tendsto_positiveMassBlock (q := 2) (by norm_num))).add_const 4).add_const
    ((2*(Real.pi:ℂ)*n)^2)
  simp_rw [Q.full_action_frequency_energyMassBlock]
  simpa only [Q.frequency.map_zero,lp.coeFn_zero,Pi.zero_apply,zero_add,Function.comp_def] using ht

/-- Even one literal full-energy action frequency has no extension continuous
at zero in any action exponent q>1, including infinity, when it agrees locally
on native nonnegative energy actions. -/
theorem no_continuous_full_action_frequency
    (Q : SourceOriginalHamiltonianData D T F H)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (h1q : 1 < q) (n : ℤ) (G : Coeff q → ℂ)
    (U : Set (Coeff q)) (hU : U ∈ 𝓝 (0:Coeff q))
    (hagree : ∀ a ∈ WeightedCoeff.nonnegativeLocus sourceEnergyActionWeight.toWeight 1,
      sourceEnergyActionsToExponent q a ∈ U →
      G (sourceEnergyActionsToExponent q a) = sourceFullActionFrequency H a n) :
    ¬ ContinuousWithinAt G (Coeff.nonnegativeLocus q) 0 := by
  let c : ℂ := (2*(Real.pi:ℂ)*n)^2
  have ht := Coeff.tendsto_positiveMassBlock h1q
  have hw : Tendsto (Coeff.positiveMassBlock q) atTop (𝓝[Coeff.nonnegativeLocus q] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Filter.Eventually.of_forall
      (Coeff.positiveMassBlock_mem_nonnegativeLocus q)⟩
  have hzero : G 0 = c := by
    have ha : (0:SourceEnergyActions) ∈ WeightedCoeff.nonnegativeLocus sourceEnergyActionWeight.toWeight 1 := by
      intro k
      constructor <;> simp
    calc
      G 0 = G (sourceEnergyActionsToExponent q 0) := by rw [map_zero]
      _ = sourceFullActionFrequency H 0 n :=
        hagree 0 ha (by simpa only [map_zero] using mem_of_mem_nhds hU)
      _ = c := Q.full_action_frequency_zero_value n
  have he : ∀ᶠ N in atTop, G (Coeff.positiveMassBlock q N) =
      sourceFullActionFrequency H (sourceEnergyMassBlock N) n := by
    filter_upwards [ht.eventually hU] with N hNU
    calc
      G (Coeff.positiveMassBlock q N) = G (sourceEnergyActionsToExponent q (sourceEnergyMassBlock N)) :=
        congrArg G (sourceEnergyMassBlock_exponent q N).symm
      _ = sourceFullActionFrequency H (sourceEnergyMassBlock N) n :=
        hagree _ (sourceEnergyMassBlock_nonnegative N)
          (by rw [sourceEnergyMassBlock_exponent]; exact hNU)
  have hlim : Tendsto (fun N => G (Coeff.positiveMassBlock q N)) atTop (𝓝 (4+c)) :=
    (Q.full_action_frequency_energyMassBlock_limit n).congr' (Filter.EventuallyEq.symm he)
  intro hG
  have hg : Tendsto (fun N => G (Coeff.positiveMassBlock q N)) atTop (𝓝 c) := by
    simpa only [hzero,Function.comp_def] using hG.tendsto.comp hw
  have hc := congrArg Complex.re (tendsto_nhds_unique hg hlim)
  norm_num only [Complex.add_re,Complex.re_ofNat] at hc
  linarith

end SourceOriginalHamiltonianData
end NLS.ZakharovShabat
