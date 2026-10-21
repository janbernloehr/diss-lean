import NLS.ZakharovShabat.SourceWeightedActionHamiltonian
import NLS.ZakharovShabat.SourceMassActionDifferential

/-! # Recovery of the actual physical H1 energy -/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem energy_weight_summable (a : ℤ → ℂ)
    (hm : Summable (fun n => ‖a n‖))
    (hk : Summable (fun n => ‖(2 * (Real.pi : ℂ) * n)^2 * a n‖)) :
    Memℓp (fun n => (sourceEnergyActionWeight.toWeight n : ℂ) * a n) 1 := by
  apply Coeff.memℓp_of_power_dominated _ _ ((hm.add hk).mul_left 2)
  intro n
  simp only [ENNReal.toReal_one, Real.rpow_one, norm_mul, Complex.norm_real,
    Real.norm_eq_abs,
    sourceEnergyActionWeight, SpectralWeight.scaledSobolev_apply, Real.rpow_two,
    norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_intCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, sq_abs]
  nlinarith [mul_nonneg (sq_nonneg (2 * Real.pi * |(n : ℝ)| - 1)) (norm_nonneg (a n))]

/-- Every original real H1 source has an actual native weighted action
sequence, with no off-domain fallback. -/
def sourceSobolevEnergyActions (a : realTypeSobolevSourceLocus) : SourceEnergyActions :=
  ⟨fun n => sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val),
    energy_weight_summable _
      (summable_sourceOrdinaryActions (by simp) (by norm_num) le_rfl
        ⟨sobolevSourceInclusion a.val, a.property⟩)
      (summable_norm_sourceSobolevWeightedAction a.val a.property)⟩

@[simp] theorem sourceSobolevEnergyActions_apply (a : realTypeSobolevSourceLocus) (n : ℤ) :
    (sourceSobolevEnergyActions a).val n =
      sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val) := rfl

theorem sourceSobolevEnergyActions_nonnegative (a : realTypeSobolevSourceLocus) :
    sourceSobolevEnergyActions a ∈
      WeightedCoeff.nonnegativeLocus sourceEnergyActionWeight.toWeight 1 := by
  intro n
  have h := sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero
    (by simp) (by norm_num) n (sobolevSourceInclusion a.val) a.property
  exact ⟨h.2.1, h.1⟩

/-- The bounded action sum is exactly the physical mass. -/
theorem sourceEnergyActionMass_sourceSobolevEnergyActions (a : realTypeSobolevSourceLocus) :
    sourceEnergyActionMass (sourceSobolevEnergyActions a) = periodOneSobolevMass a.val := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  rw [sourceEnergyActionMass_eq_tsum, periodOneSobolevMass_eq_sourceHilbertMass]
  exact (D.hilbert_complexTotalAction_eq_tsum (sobolevSourceInclusion a.val)
    (D.real_subset a.property)).symm.trans
      (D.hilbert_complexTotalAction_eq_mass ⟨sobolevSourceInclusion a.val, a.property⟩)

/-- The bounded kinetic functional is exactly the original weighted series. -/
theorem sourceEnergyActionKinetic_sourceSobolevEnergyActions (a : realTypeSobolevSourceLocus) :
    sourceEnergyActionKinetic (sourceSobolevEnergyActions a) = sourceSobolevWeightedActionSum a.val := by
  rw [sourceEnergyActionKinetic_eq_tsum, sourceSobolevWeightedActionSum_eq_tsum a.val a.property]
  rfl

namespace SourceOriginalHamiltonianData
local instance weightedActionPhysicalFourFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance weightedActionPhysicalFourHolder : (4 : ℝ≥0∞).HolderTriple 4 2 :=
  (ENNReal.holderTriple_iff _ _ _).mpr (by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- The native actions identify with those of the retained original FL4 family. -/
theorem energyActions_original (_Q : SourceOriginalHamiltonianData D T F H)
    (a : realTypeSobolevSourceLocus) :
    sourceEnergyActionsToHilbert (sourceSobolevEnergyActions a) =
      sourceActionSequence (q := 2) (by simp) (by norm_num) s (sobolevSourceFL4 a.val) := by
  ext n
  rw [sourceEnergyActionsToHilbert_apply, sourceSobolevEnergyActions_apply]
  have hc := sourceComplexAction_real_exponent (by simp) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
    (by norm_num) (by norm_num) (by norm_num : (2 : ℝ≥0∞) ≤ 4) n
    (⟨sobolevSourceInclusion a.val,a.property⟩ : realTypeSourceLocus 2)
  change sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val) =
    sourceComplexAction (by simp) (by norm_num) n (sobolevSourceFL4 a.val) at hc
  exact hc.trans (D.complex.actionSequence_apply (q := 2) (sobolevSourceFL4 a.val)
    (D.complex.real_subset (realSobolevSourceFL4 a).property) n).symm

/-- The native full action Hamiltonian recovers the actual physical energy
at every real H1 source, including infinitely many open gaps. -/
theorem full_action_physical_identity (Q : SourceOriginalHamiltonianData D T F H)
    (a : realTypeSobolevSourceLocus) :
    sourceFullActionHamiltonian H (sourceSobolevEnergyActions a) =
      periodOneSobolevHamiltonian a.val := by
  rw [sourceFullActionHamiltonian, Q.energyActions_original a,
    sourceEnergyActionMass_sourceSobolevEnergyActions,
    sourceEnergyActionKinetic_sourceSobolevEnergyActions,
    Q.physical a, sourceSobolevPhysicalCorrection]
  ring
end SourceOriginalHamiltonianData
end NLS.ZakharovShabat
