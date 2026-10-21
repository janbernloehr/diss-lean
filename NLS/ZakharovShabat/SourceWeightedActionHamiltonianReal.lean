import NLS.ZakharovShabat.SourceWeightedActionHamiltonianPhysical
import NLS.SequenceSpaces.WeightedRealCoeff

/-! # The full energy on native weighted real actions -/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem sourceEnergyActionMass_im_eq_zero (a : SourceEnergyActions)
    (ha : ∀ n, (a.val n).im = 0) : (sourceEnergyActionMass a).im = 0 := by
  rw [sourceEnergyActionMass_eq_tsum, Complex.im_tsum (sourceEnergyAction_summable a).1.of_norm]
  simp only [ha, tsum_zero]

theorem sourceEnergyActionKinetic_im_eq_zero (a : SourceEnergyActions)
    (ha : ∀ n, (a.val n).im = 0) : (sourceEnergyActionKinetic a).im = 0 := by
  rw [sourceEnergyActionKinetic_eq_tsum, Complex.im_tsum (sourceEnergyAction_summable a).2.of_norm]
  have he (n : ℤ) : ((2 * (Real.pi : ℂ) * n)^2 * a.val n).im = 0 := by
    simp [Complex.mul_im, pow_two, ha]
  simp only [he, tsum_zero]

private theorem analyticOnNhd_real_restriction
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (S : Submodule ℝ X) (U : Set X) (G : X → ℂ) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℝ (fun b : S => (G b.val).re) (Subtype.val ⁻¹' U) := by
  intro b hb
  exact (Complex.reCLM.analyticAt _).comp
    (((hG b.val hb).restrictScalars (𝕜 := ℝ)).comp (S.subtypeL.analyticAt b))

/-- The full action energy on the native weighted real subspace. -/
def sourceRealFullActionHamiltonian (H : Coeff 2 → ℂ)
    (b : WeightedRealCoeff sourceEnergyActionWeight.toWeight 1) : ℝ :=
  (sourceFullActionHamiltonian H b.val).re

/-- The original complex action domain restricted to the weighted real space. -/
def sourceRealFullActionDomain (T : Set (Coeff 2)) :
    Set (WeightedRealCoeff sourceEnergyActionWeight.toWeight 1) :=
  Subtype.val ⁻¹' (sourceEnergyActionsToHilbert ⁻¹' T)

namespace SourceOriginalHamiltonianData
local instance weightedActionRealFourFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance weightedActionRealFourHolder : (4 : ℝ≥0∞).HolderTriple 4 2 :=
  (ENNReal.holderTriple_iff _ _ _).mpr (by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

private theorem restored_im_eq_zero (h m k : ℂ)
    (hH : h.im = 0) (hm : m.im = 0) (hk : k.im = 0) :
    (h + 2 * m^2 + k).im = 0 := by
  simp [Complex.add_im, Complex.mul_im, pow_two, hH, hm, hk]

private theorem summable_correction_real (Q : SourceOriginalHamiltonianData D T F H)
    (a : Coeff 1) (ha : a ∈ Coeff.nonnegativeLocus 1) :
    (H (Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2) a)).im = 0 := by
  let b := Coeff.reCLM 1 a
  have he : RealCoeff.complexCLM 1 b = a :=
    RealCoeff.complexCLM_reCLM 1 a (fun n => (ha n).1)
  have hmem := Q.frequency.positive_actions_mem b (fun n => (ha n).2)
  rw [he] at hmem
  exact (Q.sign _ hmem (fun n => ha n)).2.1

/-- The restored physical energy is real on the entire nonnegative
weighted summable action cone. -/
theorem full_action_real (Q : SourceOriginalHamiltonianData D T F H)
    (a : SourceEnergyActions)
    (ha : a ∈ WeightedCoeff.nonnegativeLocus sourceEnergyActionWeight.toWeight 1) :
    (sourceFullActionHamiltonian H a).im = 0 :=
  restored_im_eq_zero _ _ _
    (summable_correction_real Q (sourceEnergyActionsToSummable a)
      (fun n => by simpa only [sourceEnergyActionsToSummable_apply] using ha n))
    (sourceEnergyActionMass_im_eq_zero a (fun n => (ha n).1))
    (sourceEnergyActionKinetic_im_eq_zero a (fun n => (ha n).1))

/-- Real analyticity of the named full-energy map on its original real domain. -/
theorem real_full_action_analytic (Q : SourceOriginalHamiltonianData D T F H) :
    AnalyticOnNhd ℝ (sourceRealFullActionHamiltonian H) (sourceRealFullActionDomain T) :=
  analyticOnNhd_real_restriction _ _ _ Q.full_action_analytic

/-- On every nonnegative weighted action, the real map has the exact full complex energy. -/
theorem real_full_action_values (Q : SourceOriginalHamiltonianData D T F H)
    (b : WeightedRealCoeff sourceEnergyActionWeight.toWeight 1)
    (hb : ∀ n, 0 ≤ (b.val.val n).re) :
    (sourceRealFullActionHamiltonian H b : ℂ) = sourceFullActionHamiltonian H b.val := by
  have he := Q.full_action_real b.val (fun n =>
    ⟨WeightedRealCoeff.im_eq_zero _ _ b n, hb n⟩)
  apply Complex.ext
  · rfl
  · exact he.symm

/-- One real analytic full-energy realization with the actual complex values
on the entire nonnegative weighted summable action cone. -/
theorem real_full_action_extension (Q : SourceOriginalHamiltonianData D T F H) :
    ∃ R : WeightedRealCoeff sourceEnergyActionWeight.toWeight 1 → ℝ,
      AnalyticOnNhd ℝ R (sourceRealFullActionDomain T) ∧
      ∀ b : WeightedRealCoeff sourceEnergyActionWeight.toWeight 1,
        (∀ n, 0 ≤ (b.val.val n).re) → (R b : ℂ) = sourceFullActionHamiltonian H b.val :=
  ⟨sourceRealFullActionHamiltonian H, Q.real_full_action_analytic, Q.real_full_action_values⟩
end SourceOriginalHamiltonianData
end NLS.ZakharovShabat
