import NLS.ZakharovShabat.SourceWeightedActionHamiltonianReal
import NLS.ZakharovShabat.SourceWeightedActionHamiltonianNorm
import NLS.ZakharovShabat.SourceWeightedActionHamiltonianDerivative

/-! # The full Hamiltonian on standard ell^(2,1) actions -/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The full Hamiltonian in the introductory ell^(2,1) convention,
whose weight is exactly `(1 + |n|)^2`. -/
def sourceStandardFullActionHamiltonian (H : Coeff 2 → ℂ)
    (a : WeightedCoeff (Weight.sobolev 2) 1) : ℂ :=
  sourceFullActionHamiltonian H (sourceStandardToEnergyActions a)

/-- The unchanged original domain pulled back to standard weighted actions. -/
def sourceStandardFullActionDomain (T : Set (Coeff 2)) :
    Set (WeightedCoeff (Weight.sobolev 2) 1) :=
  sourceStandardToEnergyActions ⁻¹' (sourceEnergyActionsToHilbert ⁻¹' T)

/-- The real full Hamiltonian on the standard weighted real space. -/
def sourceStandardRealFullActionHamiltonian (H : Coeff 2 → ℂ)
    (b : WeightedRealCoeff (Weight.sobolev 2) 1) : ℝ :=
  (sourceStandardFullActionHamiltonian H b.val).re

def sourceStandardRealFullActionDomain (T : Set (Coeff 2)) :
    Set (WeightedRealCoeff (Weight.sobolev 2) 1) :=
  Subtype.val ⁻¹' sourceStandardFullActionDomain T

@[simp] theorem sourceStandardToEnergyActions_toStandard (a : SourceEnergyActions) :
    sourceStandardToEnergyActions (sourceEnergyActionsToStandard a) = a :=
  sourceEnergyActionsStandardEquiv.symm_apply_apply a

@[simp] theorem sourceStandardToEnergyActions_single (n : ℤ) (c : ℂ) :
    sourceStandardToEnergyActions (WeightedCoeff.single (Weight.sobolev 2) n c) =
      WeightedCoeff.single sourceEnergyActionWeight.toWeight n c := by
  apply Subtype.ext
  funext m
  simp only [sourceStandardToEnergyActions_apply, WeightedCoeff.single_val]

/-- Literal action coefficients give the two absolutely convergent sums. -/
theorem sourceStandardFullActionHamiltonian_eq (H : Coeff 2 → ℂ)
    (a : WeightedCoeff (Weight.sobolev 2) 1) :
    sourceStandardFullActionHamiltonian H a =
      H (sourceEnergyActionsToHilbert (sourceStandardToEnergyActions a)) +
        2 * (∑' n : ℤ, a.val n)^2 + ∑' n : ℤ, (2 * (Real.pi : ℂ) * n)^2 * a.val n := by
  simp only [sourceStandardFullActionHamiltonian, sourceFullActionHamiltonian,
    sourceEnergyActionMass_eq_tsum, sourceEnergyActionKinetic_eq_tsum,
    sourceStandardToEnergyActions_apply]

private theorem standard_real_restriction
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (S : Submodule ℝ X) (U : Set X) (G : X → ℂ) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℝ (fun b : S => (G b.val).re) (Subtype.val ⁻¹' U) := by
  intro b hb
  exact (Complex.reCLM.analyticAt _).comp
    (((hG b.val hb).restrictScalars (𝕜 := ℝ)).comp (S.subtypeL.analyticAt b))

private theorem standard_analytic_precompose
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (L : X →L[ℂ] Y) (G : Y → ℂ) (U : Set Y) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℂ (fun a => G (L a)) (L ⁻¹' U) := by
  intro a ha
  exact (hG _ ha).comp (L.analyticAt a)

private theorem standard_positive_preimage
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (L : X →L[ℂ] Y) (U R : Set Y) (S : Set X)
    (hU : IsOpen U) (hR : R ⊆ U) (hS : ∀ a ∈ S, L a ∈ R) :
    IsOpen (L ⁻¹' U) ∧ S ⊆ L ⁻¹' U :=
  ⟨hU.preimage L.continuous, fun a ha => hR (hS a ha)⟩

/-- The original Hilbert actions with standard weighted input. -/
def sourceStandardActionsToHilbert : WeightedCoeff (Weight.sobolev 2) 1 →L[ℂ] Coeff 2 :=
  sourceEnergyActionsToHilbert.comp sourceStandardToEnergyActions

/-- Total action as a bounded functional on standard weighted actions. -/
def sourceStandardActionMass : WeightedCoeff (Weight.sobolev 2) 1 →L[ℂ] ℂ :=
  sourceEnergyActionMass.comp sourceStandardToEnergyActions

/-- Free energy as a bounded functional on standard weighted actions. -/
def sourceStandardActionKinetic : WeightedCoeff (Weight.sobolev 2) 1 →L[ℂ] ℂ :=
  sourceEnergyActionKinetic.comp sourceStandardToEnergyActions

private theorem standard_hilbert_single (n : ℤ) :
    sourceStandardActionsToHilbert (WeightedCoeff.single (Weight.sobolev 2) n 1) =
      lp.single 2 n 1 := by
  exact (congrArg sourceEnergyActionsToHilbert (sourceStandardToEnergyActions_single n 1)).trans
    (sourceEnergyActionsToHilbert_single n 1)

private theorem standard_mass_single (n : ℤ) :
    sourceStandardActionMass (WeightedCoeff.single (Weight.sobolev 2) n 1) = 1 := by
  exact (congrArg sourceEnergyActionMass (sourceStandardToEnergyActions_single n 1)).trans
    (sourceEnergyActionMass_single n 1)

private theorem standard_kinetic_single (n : ℤ) :
    sourceStandardActionKinetic (WeightedCoeff.single (Weight.sobolev 2) n 1) =
      (2 * (Real.pi : ℂ) * n)^2 := by
  have h := (congrArg sourceEnergyActionKinetic (sourceStandardToEnergyActions_single n 1)).trans
    (sourceEnergyActionKinetic_single n 1)
  change sourceStandardActionKinetic (WeightedCoeff.single (Weight.sobolev 2) n 1) = _ at h
  simpa only [mul_one] using h

private theorem standard_hamiltonian_formula (H : Coeff 2 → ℂ) :
    sourceStandardFullActionHamiltonian H = fun a => H (sourceStandardActionsToHilbert a) +
      2 * (sourceStandardActionMass a)^2 + sourceStandardActionKinetic a := rfl

private theorem standard_restored_line_hasDerivAt
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

private theorem standard_full_line_hasDerivAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (L : X →L[ℂ] Coeff 2) (M K : X →L[ℂ] ℂ)
    (G : X → ℂ) (H : Coeff 2 → ℂ) (F : Coeff 2 → Coeff 2) (a v : X) (n : ℤ)
    (hG : G = fun x => H (L x) + 2 * (M x)^2 + K x)
    (hH : DifferentiableAt ℂ H (L a)) (hF : F (L a) = Coeff.scalarGradient H (L a))
    (hL : L v = lp.single 2 n 1) (hM : M v = 1) (hK : K v = (2 * (Real.pi : ℂ) * n)^2) :
    HasDerivAt (fun z : ℂ => G (a + z • v))
      (F (L a) n + 4 * M a + (2 * (Real.pi : ℂ) * n)^2) 0 := by
  rw [hG]
  have hd := standard_restored_line_hasDerivAt L M K H a v hH
  simpa only [hL, hM, hK, mul_one, ← Coeff.scalarGradient_apply, ← hF] using hd

namespace SourceOriginalHamiltonianData
local instance standardActionFourFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance standardActionFourHolder : (4 : ℝ≥0∞).HolderTriple 4 2 :=
  (ENNReal.holderTriple_iff _ _ _).mpr (by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- Complex analyticity in the exact standard weighted action topology. -/
theorem standard_full_action_analytic (Q : SourceOriginalHamiltonianData D T F H) :
    AnalyticOnNhd ℂ (sourceStandardFullActionHamiltonian H)
      (sourceStandardFullActionDomain T) :=
  standard_analytic_precompose sourceStandardToEnergyActions _ _ Q.full_action_analytic

/-- The standard weighted domain is open and contains its entire positive cone. -/
theorem standard_full_action_domain (Q : SourceOriginalHamiltonianData D T F H) :
    IsOpen (sourceStandardFullActionDomain T) ∧
      WeightedCoeff.nonnegativeLocus (Weight.sobolev 2) 1 ⊆ sourceStandardFullActionDomain T :=
  standard_positive_preimage sourceStandardToEnergyActions _ _ _
    Q.full_action_domain.1 Q.full_action_domain.2
    (fun a ha n => by simpa only [sourceStandardToEnergyActions_apply] using ha n)

theorem standard_real_full_action_analytic (Q : SourceOriginalHamiltonianData D T F H) :
    AnalyticOnNhd ℝ (sourceStandardRealFullActionHamiltonian H)
      (sourceStandardRealFullActionDomain T) :=
  standard_real_restriction _ _ _ Q.standard_full_action_analytic

/-- The real realization preserves the full complex value on every positive action. -/
theorem standard_real_full_action_values (Q : SourceOriginalHamiltonianData D T F H)
    (b : WeightedRealCoeff (Weight.sobolev 2) 1) (hb : ∀ n, 0 ≤ (b.val.val n).re) :
    (sourceStandardRealFullActionHamiltonian H b : ℂ) =
      sourceStandardFullActionHamiltonian H b.val := by
  have he := Q.full_action_real (sourceStandardToEnergyActions b.val) (fun n => by
    simpa only [sourceStandardToEnergyActions_apply] using
      And.intro (WeightedRealCoeff.im_eq_zero _ _ b n) (hb n))
  apply Complex.ext
  · rfl
  · exact he.symm

/-- The standard weighted action formula is the physical H1 energy for every source. -/
theorem standard_full_action_physical_identity (Q : SourceOriginalHamiltonianData D T F H)
    (a : realTypeSobolevSourceLocus) :
    sourceStandardFullActionHamiltonian H
      (sourceEnergyActionsToStandard (sourceSobolevEnergyActions a)) =
      periodOneSobolevHamiltonian a.val := by
  rw [sourceStandardFullActionHamiltonian, sourceStandardToEnergyActions_toStandard]
  exact Q.full_action_physical_identity a

/-- Literal standard action differentiation restores the original physical frequency. -/
theorem standard_full_action_coordinate_derivative (Q : SourceOriginalHamiltonianData D T F H)
    (a : WeightedCoeff (Weight.sobolev 2) 1) (ha : sourceStandardActionsToHilbert a ∈ T) (n : ℤ) :
    HasDerivAt (fun z : ℂ => sourceStandardFullActionHamiltonian H
      (a + z • WeightedCoeff.single (Weight.sobolev 2) n 1))
      (F (sourceStandardActionsToHilbert a) n + 4 * sourceStandardActionMass a +
        (2 * (Real.pi : ℂ) * n)^2) 0 :=
  standard_full_line_hasDerivAt sourceStandardActionsToHilbert sourceStandardActionMass
    sourceStandardActionKinetic (sourceStandardFullActionHamiltonian H) H F a
    (WeightedCoeff.single (Weight.sobolev 2) n 1) n (standard_hamiltonian_formula H)
    (Q.analytic _ ha).differentiableAt (Q.gradient_eq ha)
    (standard_hilbert_single n) (standard_mass_single n) (standard_kinetic_single n)


end SourceOriginalHamiltonianData
end NLS.ZakharovShabat
