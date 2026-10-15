import NLS.ZakharovShabat.SourcePrimitivePowerHamiltonian
import NLS.ZakharovShabat.SourceSection18HamiltonianCorrection
/-! # Formal witnesses for the Section 21 sign corrections

Equation (4.13) omits the minus before the cubic moment sum. The proofs
on p. 98 twice say nonnegative where nonpositive is required. Actual
unit-mass sources refute these printed signs for the original quantities.
-/
noncomputable section
open Set Filter Topology NLS NLS.ZakharovShabat
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas

/-- An actual real finite-gap source refutes the printed positive cubic term. -/
theorem printed_lemma21_2_sign_counterexample
    {W : Set (CoeffPair 2)} (P : SourcePrimitivePowerAtlas (by simp) (by norm_num) W) :
    ∃ φ : realTypeSourceLocus 2, ∃ hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num),
      sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 3-
        2*(sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1)^2-
          (∑' n : ℤ, (2*(n:ℂ)*Real.pi)^2*sourceComplexAction (by simp) (by norm_num) n φ.val) ≠
            (4/3:ℂ)*(∑' n : ℤ, P.moment n 3 φ.val) := by
  obtain ⟨a,ha,_,_⟩ := exists_realSobolev_single_action 0 1 (by norm_num)
  let φ : realTypeSourceLocus 2 := ⟨sobolevSourceInclusion a.val,a.property⟩
  have hclosed (n : ℤ) (hn : n ≠ 0) : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n = 0 := by
    have hact : sourceComplexAction (by simp) (by norm_num) n φ.val = 0 := by
      change sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val) = 0
      simp only [ha n,if_neg hn]
    have h := (sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
      n φ.val φ.property).2.2.mp hact
    simpa only [sourcePeriodicGapDisplacement_apply] using h
  have hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
    apply (Set.finite_singleton (0 : ℤ)).subset
    intro n hn
    by_contra hn0
    exact hn (hclosed n hn0)
  have hopen : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) 0 ≠ 0 := by
    intro hz
    have he := (sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
      0 φ.val φ.property).2.2.mpr (by simpa only [sourcePeriodicGapDisplacement_apply] using hz)
    change sourceComplexAction (by simp) (by norm_num) 0 (sobolevSourceInclusion a.val) = 0 at he
    rw [ha 0] at he
    norm_num at he
  have hs : (∑' n : ℤ, P.moment n 3 φ.val) = P.moment 0 3 φ.val :=
    tsum_eq_single 0 (fun n hn => P.moment_of_collapsed φ.val
      (P.realType_subset_domain φ.property) n (hclosed n hn) 3)
  have hpos : 0 < (P.moment 0 3 φ.val).re := P.real_odd_moment_pos φ 0 1 hopen
  refine ⟨φ,hf,?_⟩
  rw [P.finiteGap_hamiltonian_identity φ hf,hs]
  intro he
  have hz : P.moment 0 3 φ.val = 0 := by
    linear_combination (-3/8:ℂ)*he
  rw [hz] at hpos
  exact (lt_irrefl 0) hpos
end NLS.ZakharovShabat.SourcePrimitivePowerAtlas

namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
open scoped ENNReal
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The source Hamiltonian is strictly negative at a constructed unit-mass H¹ source. -/
theorem printed_nonnegative_hamiltonian_counterexample
    {W : Set (CoeffPair 4)} (P : SourcePrimitivePowerAtlas (by simp) (by norm_num) W) :
    ∃ a : realTypeSobolevSourceLocus, periodOneSobolevMass a.val = 1 ∧
      (P.renormalizedHamiltonian (sobolevSourceFL4 a.val)).re < 0 := by
  obtain ⟨a,_,hm,_⟩ := exists_realSobolev_single_action 0 1 (by norm_num)
  have hmass : periodOneSobolevMass a.val = 1 := by simpa using hm
  have hane : a.val ≠ 0 := by
    intro hz
    simp [hz,periodOneSobolevMass] at hmass
  have hne := (sourceSobolevPhysicalCorrection_eq_zero_iff a).not.mpr hane
  refine ⟨a,hmass,?_⟩
  rw [P.renormalizedHamiltonian_eq_sobolevPhysicalCorrection a]
  have hsign := sourceSobolevPhysicalCorrection_nonpos a
  apply lt_of_le_of_ne hsign.1
  intro he
  exact hne (Complex.ext he hsign.2)
end NLS.ZakharovShabat.SourcePrimitivePowerAtlas

namespace NLS.ZakharovShabat.SourceOriginalHamiltonianData
open scoped ENNReal
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

/-- The same strictly negative value lies in the original action Hamiltonian domain. -/
theorem printed_nonnegative_action_hamiltonian_counterexample
    {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}
    (E : SourceOriginalHamiltonianData D T F H) :
    ∃ a : realTypeSobolevSourceLocus, periodOneSobolevMass a.val = 1 ∧
      sourceActionSequence (q := 2) (by simp) (by norm_num) s (sobolevSourceFL4 a.val) ∈ T ∧
      sourceActionSequence (q := 2) (by simp) (by norm_num) s (sobolevSourceFL4 a.val) ∈
        Coeff.nonnegativeLocus 2 ∧
      (H (sourceActionSequence (q := 2) (by simp) (by norm_num) s (sobolevSourceFL4 a.val))).re < 0 := by
  obtain ⟨Wp,P,he⟩ := E.spectral
  obtain ⟨a,hm,hn⟩ := P.printed_nonnegative_hamiltonian_counterexample
  refine ⟨a,hm,E.frequency.real_actions_mem (realSobolevSourceFL4 a),
    D.complex.actionSequence_mem_nonnegativeLocus (realSobolevSourceFL4 a),?_⟩
  have hrec : H (sourceActionSequence (q := 2) (by simp) (by norm_num) s (sobolevSourceFL4 a.val)) =
      P.renormalizedHamiltonian (sobolevSourceFL4 a.val) := by
    simpa only using! he (realSobolevSourceFL4 a)
  rw [hrec]
  exact hn
end NLS.ZakharovShabat.SourceOriginalHamiltonianData
