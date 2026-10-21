import NLS.ZakharovShabat.SourceHamiltonianOriginal
import NLS.SequenceSpaces.ShiftedWeight
import NLS.SequenceSpaces.WeightedNonnegativeActions

/-! # The full Hamiltonian on weighted summable actions -/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The physical order-two weight on action sequences. -/
def sourceEnergyActionWeight : SpectralWeight :=
  SpectralWeight.scaledSobolev (2 * Real.pi) 2 (by positivity) (by norm_num)

/-- Native weighted summable actions, with their literal coordinates. -/
abbrev SourceEnergyActions := WeightedCoeff sourceEnergyActionWeight.toWeight 1

/-- The unweighted summable sequence retains every action coordinate. -/
def sourceEnergyActionsToSummable : SourceEnergyActions →L[ℂ] Coeff 1 :=
  sourceEnergyActionWeight.toCoeff

@[simp] theorem sourceEnergyActionsToSummable_apply (a : SourceEnergyActions) (n : ℤ) :
    sourceEnergyActionsToSummable a n = a.val n :=
  sourceEnergyActionWeight.toCoeff_apply a n

/-- The same actions in the Hilbert domain of the renormalized Hamiltonian. -/
def sourceEnergyActionsToHilbert : SourceEnergyActions →L[ℂ] Coeff 2 :=
  (Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)).comp
    sourceEnergyActionsToSummable

@[simp] theorem sourceEnergyActionsToHilbert_apply (a : SourceEnergyActions) (n : ℤ) :
    sourceEnergyActionsToHilbert a n = a.val n := by
  exact sourceEnergyActionsToSummable_apply a n

/-- Summing the actions is a bounded linear functional in the native weighted norm. -/
def sourceEnergyActionMass : SourceEnergyActions →L[ℂ] ℂ :=
  (lp.tsumCLM ℂ ℤ ℂ).comp sourceEnergyActionsToSummable

theorem sourceEnergyActionMass_eq_tsum (a : SourceEnergyActions) :
    sourceEnergyActionMass a = ∑' n : ℤ, a.val n := by
  change (∑' n : ℤ, sourceEnergyActionsToSummable a n) = _
  simp only [sourceEnergyActionsToSummable_apply]

private theorem sourceEnergyAction_kinetic_bound (n : ℤ) :
    Weight.one n * ‖(2 * (Real.pi : ℂ) * n)^2‖ ≤
      1 * sourceEnergyActionWeight.toWeight n := by
  simp only [Weight.one_apply, one_mul, norm_pow, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_intCast, sourceEnergyActionWeight,
    SpectralWeight.scaledSobolev_apply, Real.rpow_two]
  nlinarith [mul_nonneg Real.pi_pos.le (abs_nonneg (n : ℝ))]

/-- The kinetic-weighted sequence is bounded and linear into ell1. -/
def sourceEnergyActionKineticSequence : SourceEnergyActions →L[ℂ] Coeff 1 :=
  (WeightedCoeff.weightIsometry Weight.one 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.weightedMultiplierCLM sourceEnergyActionWeight.toWeight Weight.one
      (fun n => (2 * (Real.pi : ℂ) * n)^2) 1 zero_le_one sourceEnergyAction_kinetic_bound)

@[simp] theorem sourceEnergyActionKineticSequence_apply (a : SourceEnergyActions) (n : ℤ) :
    sourceEnergyActionKineticSequence a n = (2 * (Real.pi : ℂ) * n)^2 * a.val n := by
  change (1 : ℂ) * ((2 * (Real.pi : ℂ) * n)^2 * a.val n) = _
  exact one_mul _

/-- The weighted linear term in the full physical energy. -/
def sourceEnergyActionKinetic : SourceEnergyActions →L[ℂ] ℂ :=
  (lp.tsumCLM ℂ ℤ ℂ).comp sourceEnergyActionKineticSequence

theorem sourceEnergyActionKinetic_eq_tsum (a : SourceEnergyActions) :
    sourceEnergyActionKinetic a = ∑' n : ℤ, (2 * (Real.pi : ℂ) * n)^2 * a.val n := by
  change (∑' n : ℤ, sourceEnergyActionKineticSequence a n) = _
  simp only [sourceEnergyActionKineticSequence_apply]

/-- Both physical action sums converge absolutely on the full native space. -/
theorem sourceEnergyAction_summable (a : SourceEnergyActions) :
    Summable (fun n : ℤ => ‖a.val n‖) ∧
      Summable (fun n : ℤ => ‖(2 * (Real.pi : ℂ) * n)^2 * a.val n‖) := by
  constructor
  · simpa only [sourceEnergyActionsToSummable_apply] using
      (sourceEnergyActionsToSummable a).property.norm.summable_of_one
  · simpa only [sourceEnergyActionKineticSequence_apply] using
      (sourceEnergyActionKineticSequence a).property.norm.summable_of_one

/-- Restore the mass and free dispersion to the same renormalized Hamiltonian. -/
def sourceFullActionHamiltonian (H : Coeff 2 → ℂ) (a : SourceEnergyActions) : ℂ :=
  H (sourceEnergyActionsToHilbert a) + 2 * (sourceEnergyActionMass a)^2 +
    sourceEnergyActionKinetic a

private theorem analyticOnNhd_restored_actionHamiltonian
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (L : X →L[ℂ] Coeff 2) (M K : X →L[ℂ] ℂ)
    (T : Set (Coeff 2)) (H : Coeff 2 → ℂ) (hH : AnalyticOnNhd ℂ H T) :
    AnalyticOnNhd ℂ (fun a => H (L a) + 2 * (M a)^2 + K a) (L ⁻¹' T) := by
  intro a ha
  exact (((hH _ ha).comp (L.analyticAt a)).add
    (analyticAt_const.mul ((M.analyticAt a).pow 2))).add (K.analyticAt a)

namespace SourceOriginalHamiltonianData
local instance weightedActionHamiltonianFourFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance weightedActionHamiltonianFourHolder : (4 : ℝ≥0∞).HolderTriple 4 2 :=
  (ENNReal.holderTriple_iff _ _ _).mpr (by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- The full physical action energy is analytic on the inverse image of
the unchanged original Hamiltonian domain. -/
theorem full_action_analytic (Q : SourceOriginalHamiltonianData D T F H) :
    AnalyticOnNhd ℂ (sourceFullActionHamiltonian H)
      (sourceEnergyActionsToHilbert ⁻¹' T) :=
  analyticOnNhd_restored_actionHamiltonian sourceEnergyActionsToHilbert
    sourceEnergyActionMass sourceEnergyActionKinetic T H Q.analytic

private theorem positive_summable_mem (Q : SourceOriginalHamiltonianData D T F H)
    (a : Coeff 1) (ha : a ∈ Coeff.nonnegativeLocus 1) :
    Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2) a ∈ T := by
  let b := Coeff.reCLM 1 a
  have hb : ∀ n, 0 ≤ b n := fun n => (ha n).2
  have he : RealCoeff.complexCLM 1 b = a :=
    RealCoeff.complexCLM_reCLM 1 _ (fun n => (ha n).1)
  have h := Q.frequency.positive_actions_mem b hb
  rw [he] at h
  exact h

private theorem positive_inclusion_domain (Q : SourceOriginalHamiltonianData D T F H)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (L : X →L[ℂ] Coeff 1) (S : Set X)
    (hS : ∀ a ∈ S, L a ∈ Coeff.nonnegativeLocus 1) :
    IsOpen (((Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)).comp L) ⁻¹' T) ∧
      S ⊆ ((Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)).comp L) ⁻¹' T :=
  ⟨Q.frequency.isOpen.preimage
      ((Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)).comp L).continuous,
    fun a ha => positive_summable_mem Q (L a) (hS a ha)⟩

/-- The native full-energy domain is open and contains the entire
nonnegative weighted action cone. -/
theorem full_action_domain (Q : SourceOriginalHamiltonianData D T F H) :
    IsOpen (sourceEnergyActionsToHilbert ⁻¹' T) ∧
      WeightedCoeff.nonnegativeLocus sourceEnergyActionWeight.toWeight 1 ⊆
        sourceEnergyActionsToHilbert ⁻¹' T :=
  positive_inclusion_domain Q sourceEnergyActionsToSummable _
    (fun a ha n => by simpa only [sourceEnergyActionsToSummable_apply] using ha n)
end SourceOriginalHamiltonianData
end NLS.ZakharovShabat
