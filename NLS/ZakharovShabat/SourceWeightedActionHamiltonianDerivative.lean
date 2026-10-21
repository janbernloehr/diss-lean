import NLS.ZakharovShabat.SourceWeightedActionHamiltonianPhysical
import NLS.SequenceSpaces.WeightedSingle

/-! # Literal weighted action derivatives of full energy -/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem sourceEnergyActionsToHilbert_single (n : ℤ) (c : ℂ) :
    sourceEnergyActionsToHilbert (WeightedCoeff.single sourceEnergyActionWeight.toWeight n c) =
      lp.single 2 n c := by
  ext m
  simp only [sourceEnergyActionsToHilbert_apply, WeightedCoeff.single_val, lp.single_apply]

theorem sourceEnergyActionMass_single (n : ℤ) (c : ℂ) :
    sourceEnergyActionMass (WeightedCoeff.single sourceEnergyActionWeight.toWeight n c) = c := by
  rw [sourceEnergyActionMass_eq_tsum]
  simp [WeightedCoeff.single_val]

theorem sourceEnergyActionKinetic_single (n : ℤ) (c : ℂ) :
    sourceEnergyActionKinetic (WeightedCoeff.single sourceEnergyActionWeight.toWeight n c) =
      (2 * (Real.pi : ℂ) * n)^2 * c := by
  rw [sourceEnergyActionKinetic_eq_tsum]
  simp [WeightedCoeff.single_val, Pi.single_apply]

private theorem restored_line_hasDerivAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (L : X →L[ℂ] Coeff 2) (M K : X →L[ℂ] ℂ) (H : Coeff 2 → ℂ)
    (a v : X) (hH : DifferentiableAt ℂ H (L a)) :
    HasDerivAt (fun z : ℂ => H (L (a + z • v)) + 2 * (M (a + z • v))^2 + K (a + z • v))
      (fderiv ℂ H (L a) (L v) + 4 * M a * M v + K v) 0 := by
  have hline : HasDerivAt (fun z : ℂ => a + z • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add a
  have hL : HasDerivAt (fun z : ℂ => L (a + z • v)) (L v) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 hline
  have hf : HasDerivAt (fun z : ℂ => H (L (a + z • v))) (fderiv ℂ H (L a) (L v)) 0 := by
    apply HasFDerivAt.comp_hasDerivAt 0 _ hL
    simpa using hH.hasFDerivAt
  have hm : HasDerivAt (fun z : ℂ => M (a + z • v)) (M v) 0 :=
    M.hasFDerivAt.comp_hasDerivAt 0 hline
  have hk : HasDerivAt (fun z : ℂ => K (a + z • v)) (K v) 0 :=
    K.hasFDerivAt.comp_hasDerivAt 0 hline
  convert! (hf.add ((hm.pow 2).const_mul 2)).add hk using 1
  simp only [zero_smul, add_zero, Nat.add_one_sub_one, pow_one, Nat.cast_ofNat]
  ring

namespace SourceOriginalHamiltonianData
local instance weightedActionDerivativeFourFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance weightedActionDerivativeFourHolder : (4 : ℝ≥0∞).HolderTriple 4 2 :=
  (ENNReal.holderTriple_iff _ _ _).mpr (by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- Each literal action derivative is the retained frequency with physical
mass and free dispersion restored, throughout the original complex domain. -/
theorem full_action_coordinate_derivative (Q : SourceOriginalHamiltonianData D T F H)
    (a : SourceEnergyActions) (ha : sourceEnergyActionsToHilbert a ∈ T) (n : ℤ) :
    HasDerivAt (fun z : ℂ => sourceFullActionHamiltonian H
      (a + z • WeightedCoeff.single sourceEnergyActionWeight.toWeight n 1))
      (F (sourceEnergyActionsToHilbert a) n + 4 * sourceEnergyActionMass a +
        (2 * (Real.pi : ℂ) * n)^2) 0 := by
  have hd := restored_line_hasDerivAt sourceEnergyActionsToHilbert sourceEnergyActionMass
    sourceEnergyActionKinetic H a (WeightedCoeff.single sourceEnergyActionWeight.toWeight n 1)
    (Q.analytic _ ha).differentiableAt
  simpa only [sourceFullActionHamiltonian, sourceEnergyActionsToHilbert_single,
    sourceEnergyActionMass_single, sourceEnergyActionKinetic_single, mul_one,
    ← Coeff.scalarGradient_apply, ← Q.gradient_eq ha] using hd
end SourceOriginalHamiltonianData
end NLS.ZakharovShabat
