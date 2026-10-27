import NLS.ZakharovShabat.SourceOrdinaryFrequencyAsymptotic
import NLS.ZakharovShabat.SourceWeightedActionHamiltonianDerivative
import NLS.SequenceSpaces.PairExponentIdentity

/-! # Ordinary frequencies as derivatives of the full physical energy

The literal action derivatives of the full Hamiltonian equal the original
ordinary phase frequencies at every real H1 source. Their remainder after
free dispersion tends to four times the actual physical mass. The bounds
include every signed index and do not assume finite gap.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The literal coordinate derivative of the full energy in native weighted actions. -/
def sourceFullActionFrequency (H : Coeff 2 → ℂ) (a : SourceEnergyActions) (n : ℤ) : ℂ :=
  deriv (fun z : ℂ => sourceFullActionHamiltonian H
    (a + z • WeightedCoeff.single sourceEnergyActionWeight.toWeight n 1)) 0

/-- The physical Sobolev mass equals the ordinary scalar mass of the same source. -/
theorem periodOneSobolevMass_eq_ordinaryMass (a : realTypeSobolevSourceLocus) :
    periodOneSobolevMass a.val =
      (sourceOrdinaryMass le_rfl ⟨sobolevSourceInclusion a.val,a.property⟩ : ℂ) := by
  rw [sourceOrdinaryMass_complex,sourceOrdinaryComplexMass,
    CoeffPair.exponentInclusion_refl, periodOneSobolevMass_eq_sourceHilbertMass]

namespace SourceOriginalHamiltonianData
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 :=
  (ENNReal.holderTriple_iff _ _ _).mpr (by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}
  (E : SourceOriginalHamiltonianData D T F H)

include E

/-- On the actual domain this derivative is the original frequency with mass and dispersion restored. -/
theorem full_action_frequency_eq (a : SourceEnergyActions)
    (ha : sourceEnergyActionsToHilbert a ∈ T) (n : ℤ) :
    sourceFullActionFrequency H a n = F (sourceEnergyActionsToHilbert a) n +
      4*sourceEnergyActionMass a + (2*(Real.pi : ℂ)*n)^2 :=
  (E.full_action_coordinate_derivative a ha n).deriv

/-- Every physical H1 input lies in the domain of the literal coordinate derivative. -/
theorem full_action_frequency_physical (a : realTypeSobolevSourceLocus) (n : ℤ) :
    sourceFullActionFrequency H (sourceSobolevEnergyActions a) n =
      F (sourceEnergyActionsToHilbert (sourceSobolevEnergyActions a)) n +
        4*periodOneSobolevMass a.val + (2*(Real.pi : ℂ)*n)^2 := by
  have hm : sourceEnergyActionsToHilbert (sourceSobolevEnergyActions a) ∈ T := by
    rw [E.energyActions_original a]
    exact E.frequency.real_actions_mem (realSobolevSourceFL4 a)
  rw [E.full_action_frequency_eq _ hm,sourceEnergyActionMass_sourceSobolevEnergyActions]

/-- The actual physical action derivative agrees with any retained original Hilbert moment family. -/
theorem full_action_frequency_ordinary
    {W₂ X₂ V₂ Wa₂ B₂ U₂ : Set (CoeffPair 2)}
    {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D₂ : SourceSection17OriginalData (by simp) (by norm_num) W₂ X₂ V₂ s₂}
    {A₂ : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa₂ s₂}
    (Q₂ : SourceSection20Data D₂ A₂ B₂ U₂) (a : realTypeSobolevSourceLocus) (n : ℤ) :
    sourceFullActionFrequency H (sourceSobolevEnergyActions a) n =
      (A₂.ordinaryPhaseFrequency le_rfl ⟨sobolevSourceInclusion a.val,a.property⟩ n : ℂ) := by
  obtain ⟨Wa₄,A₄,B₄,U₄,Q₄⟩ := D.exists_section20
  have hf : F (sourceEnergyActionsToHilbert (sourceSobolevEnergyActions a)) n =
      A₂.renormalizedFrequency n (sobolevSourceInclusion a.val) := by
    rw [E.energyActions_original a]
    exact (Q₄.action_frequency E.frequency (realSobolevSourceFL4 a) n).trans
      (Q₄.frequency_eq_of_coefficients Q₂ (realSobolevSourceFL4 a)
        ⟨sobolevSourceInclusion a.val,a.property⟩ (fun _ => ⟨rfl,rfl⟩) n)
  rw [E.full_action_frequency_physical a n,hf,
    A₂.ordinaryPhaseFrequency_complex Q₂.roots.toSourcePsiIsolatingComplexExtension]
  rw [periodOneSobolevMass_eq_ordinaryMass,sourceOrdinaryMass_complex]
  ring

/-- At every real H1 input the ordinary frequency remainder tends to the physical mass shift. -/
theorem full_action_frequency_mass_limit (a : realTypeSobolevSourceLocus) :
    Tendsto (fun n : ℤ => sourceFullActionFrequency H (sourceSobolevEnergyActions a) n -
      (2*(Real.pi : ℂ)*n)^2) cofinite (𝓝 (4*periodOneSobolevMass a.val)) := by
  have ht : Tendsto
      (fun n : ℤ => F (sourceEnergyActionsToHilbert (sourceSobolevEnergyActions a)) n)
      cofinite (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
        (Coeff.tendsto_norm_apply_cofinite (by simp) _)
  have he (n : ℤ) : sourceFullActionFrequency H (sourceSobolevEnergyActions a) n -
      (2*(Real.pi : ℂ)*n)^2 =
      F (sourceEnergyActionsToHilbert (sourceSobolevEnergyActions a)) n + 4*periodOneSobolevMass a.val := by
    rw [E.full_action_frequency_physical a n]
    ring
  simp_rw [he]
  simpa using ht.add_const (4*periodOneSobolevMass a.val)

/-- A quantitative bound for every index uses the literal full-energy derivative. -/
theorem full_action_frequency_remainder_bound (a : realTypeSobolevSourceLocus) (n : ℤ) :
    ‖sourceFullActionFrequency H (sourceSobolevEnergyActions a) n - (2*(Real.pi : ℂ)*n)^2‖ ≤
      ‖F (sourceEnergyActionsToHilbert (sourceSobolevEnergyActions a))‖ + 4*‖periodOneSobolevMass a.val‖ := by
  rw [E.full_action_frequency_physical a n,add_sub_cancel_right]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  norm_num
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (F (sourceEnergyActionsToHilbert (sourceSobolevEnergyActions a))) n

end SourceOriginalHamiltonianData
end NLS.ZakharovShabat
