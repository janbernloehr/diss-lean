import NLS.ZakharovShabat.SourceStandardRootNorm
import Mathlib.Tactic.Linarith

/-!
# Square-root growth at complex periodic endpoints

The modulus of the selected standard root is the square root of the
product of its two endpoint distances. Close to either endpoint, the
other endpoint stays at least half a gap length away. No reality or
ordering assumption on the endpoints is needed.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A uniform radial lower bound works at either complex endpoint. -/
theorem sourceStandardRoot_complexEndpoint_norm_lower_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c z : ℂ)
    (hc : c ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ))
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ m)
    (hnear : ‖c-z‖ ≤ ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m - canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m‖ / 2) :
    Real.sqrt ((‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m -
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖ / 2) *
        ‖c-z‖) ≤ ‖sourceStandardRoot hp hp1 ψ m z‖ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let d := ‖r-l‖ / 2
  let R := sourceStandardRoot hp hp1 ψ m z
  have hd : 0 ≤ d := div_nonneg (norm_nonneg _) (by norm_num)
  have hsq : ‖R‖ ^ 2 = ‖l-z‖ * ‖r-z‖ := sourceStandardRoot_norm_sq hp hp1 ψ m z hz
  have htri : ‖r-l‖ ≤ ‖r-z‖ + ‖l-z‖ := by
    calc
      ‖r-l‖ = ‖(r-z)-(l-z)‖ := by congr 1; ring
      _ ≤ ‖r-z‖ + ‖l-z‖ := norm_sub_le _ _
  have hprod : d * ‖c-z‖ ≤ ‖R‖ ^ 2 := by
    simp only [mem_insert_iff, mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · have hlong : d ≤ ‖r-z‖ := by
        change ‖l-z‖ ≤ d at hnear
        dsimp [d] at *
        linarith only [htri,hnear]
      rw [hsq]
      exact (mul_le_mul_of_nonneg_right hlong (norm_nonneg _)).trans_eq (mul_comm _ _)
    · have hlong : d ≤ ‖l-z‖ := by
        change ‖r-z‖ ≤ d at hnear
        dsimp [d] at *
        linarith only [htri,hnear]
      rw [hsq]
      exact mul_le_mul_of_nonneg_right hlong (norm_nonneg _)
  have hdsq : Real.sqrt (d * ‖c-z‖) ^ 2 = d * ‖c-z‖ :=
    Real.sq_sqrt (mul_nonneg hd (norm_nonneg _))
  change Real.sqrt (d * ‖c-z‖) ≤ ‖R‖
  nlinarith only [hdsq,hprod,Real.sqrt_nonneg (d * ‖c-z‖),norm_nonneg R]

end NLS.ZakharovShabat
