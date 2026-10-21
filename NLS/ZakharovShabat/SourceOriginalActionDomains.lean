import NLS.ZakharovShabat.SourceHamiltonianOriginal
import NLS.SequenceSpaces.NonnegativeActionDensity

/-! # The original positive action domains

The retained frequency and Hamiltonian have relatively open dense positive
domains, and the same Hamiltonian has an exact real summable-action realization.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

namespace SourceOriginalFrequencyData
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
  {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {U : Set (Coeff q)} {F : Coeff q → Coeff q}

/-- The same original frequency domain is open and dense relative to its
nonnegative action cone; no replacement domain or map is chosen. -/
theorem positive_domain (E : SourceOriginalFrequencyData D U F) :
    IsOpen {b : Coeff.nonnegativeLocus q | b.val ∈ U} ∧
      Dense {b : Coeff.nonnegativeLocus q | b.val ∈ U} :=
  Coeff.isOpen_dense_nonnegative_domain (Coeff.doublingExponent_ne_top hp)
    U E.isOpen E.positive_actions_mem
end SourceOriginalFrequencyData

namespace SourceOriginalHamiltonianData
local instance originalActionDomainsFourFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance originalActionDomainsFourHolder : (4 : ℝ≥0∞).HolderTriple 4 2 :=
  (ENNReal.holderTriple_iff _ _ _).mpr (by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- The positive part of the retained Hamiltonian domain is relatively
open and dense in the entire nonnegative Hilbert action cone. -/
theorem positive_domain (Q : SourceOriginalHamiltonianData D T F H) :
    IsOpen {b : Coeff.nonnegativeLocus 2 | b.val ∈ T} ∧
      Dense {b : Coeff.nonnegativeLocus 2 | b.val ∈ T} :=
  Q.frequency.positive_domain

/-- The original Hamiltonian has a real analytic summable-action
realization, with its actual values and sign on the full positive cone. -/
theorem real_summable_extension (Q : SourceOriginalHamiltonianData D T F H) :
    ∃ R : RealCoeff 1 → ℝ,
      AnalyticOnNhd ℝ R ((fun b : RealCoeff 1 =>
        Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (RealCoeff.complexCLM 1 b)) ⁻¹' T) ∧
      ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
        (R b : ℂ) = H (Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (RealCoeff.complexCLM 1 b)) ∧ R b ≤ 0 ∧ (R b = 0 ↔ b = 0) := by
  let L := ((Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)).restrictScalars ℝ).comp
    (RealCoeff.complexCLM 1)
  refine ⟨fun b => (H (L b)).re, ?_, ?_⟩
  · intro b hb
    exact (Complex.reCLM.analyticAt _).comp
      (((Q.analytic (L b) hb).restrictScalars (𝕜 := ℝ)).comp (L.analyticAt b))
  · intro b hb
    have hmem : L b ∈ T := Q.frequency.positive_actions_mem b hb
    have hpos : L b ∈ Coeff.nonnegativeLocus 2 := fun n => ⟨rfl, hb n⟩
    obtain ⟨hle, him, hzero⟩ := Q.sign (L b) hmem hpos
    have hval : ((H (L b)).re : ℂ) = H (L b) := by
      apply Complex.ext <;> simp [him]
    refine ⟨hval, hle, ?_⟩
    constructor
    · intro hz
      change (H (L b)).re = 0 at hz
      have hL : L b = 0 := hzero.mp (by rw [← hval, hz]; rfl)
      ext n
      have he := congrArg (fun a : Coeff 2 => (a n).re) hL
      exact he
    · intro hz
      subst b
      have he := hzero.mpr L.map_zero
      change (H (L 0)).re = 0
      rw [he]
      rfl
end SourceOriginalHamiltonianData
end NLS.ZakharovShabat
