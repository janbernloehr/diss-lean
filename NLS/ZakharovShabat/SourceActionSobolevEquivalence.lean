import NLS.SequenceSpaces.RealActionWeightedMembership
import NLS.ZakharovShabat.SourceActionTorus
import NLS.ZakharovShabat.SourceBirkhoffSobolevRegularity

/-! # Equal original actions preserve every nonnegative Sobolev order -/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ B W : Set (CoeffPair p)} {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- All nonnegative real Sobolev regularities are shared by sources with
the same original spectral actions, for every finite Banach exponent p>1. -/
theorem source_sobolev_mem_iff_of_actions_eq
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ ψ : realTypeSourceSubmodule p)
    (ha : ∀ n, (sourceRealAction hp hp1 φ.val φ.property n).re =
      (sourceRealAction hp hp1 ψ.val ψ.property n).re) (t : ℝ) (ht : 0 ≤ t) :
    (Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*φ.val.fst n) p ∧
      Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*φ.val.snd n) p) ↔
    (Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*ψ.val.fst n) p ∧
      Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*ψ.val.snd n) p) := by
  rw [D.source_sobolev_mem_iff_real_map_mem φ t ht,D.source_sobolev_mem_iff_real_map_mem ψ t ht]
  have he (n : ℤ) : RealCoeff.pairAction (sourceRealBirkhoffMap hp hp1 s φ) n =
      RealCoeff.pairAction (sourceRealBirkhoffMap hp hp1 s ψ) n := by
    rw [D.real_pairAction_eq,D.real_pairAction_eq,ha n]
  exact ⟨fun h => RealCoeff.weighted_mem_of_pairAction_eq (Weight.sobolev t) _ _ h (fun n => (he n).symm),
    fun h => RealCoeff.weighted_mem_of_pairAction_eq (Weight.sobolev t) _ _ h he⟩

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
