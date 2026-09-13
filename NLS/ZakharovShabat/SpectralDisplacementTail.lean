import NLS.ZakharovShabat.RootDisplacementSequence

/-!
# Displacement power tails of a spectral sequence

A summable high-frequency majorant gives the quantitative power tail.
Only finitely many signed modes are excluded, so the complete displacement
sequence belongs to the actual coefficient space at every finite positive exponent.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The displacement power of one spectral sequence on the signed tail. -/
def spectralDisplacementPowerTail (p : ℝ≥0∞) (N : ℕ) (ζ : ℤ → ℂ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then ‖ζ n-(Real.pi : ℂ)*n‖^p.toReal else 0

/-- Pointwise domination by a summable sequence gives convergence and a genuine sum bound. -/
theorem spectralDisplacementPowerTail_summable_and_le (p : ℝ≥0∞) (N : ℕ) (ζ : ℤ → ℂ)
    (M : ℤ → ℝ) (hs : Summable M)
    (hb : ∀ n : ℤ, spectralDisplacementPowerTail p N ζ n ≤ M n) :
    Summable (spectralDisplacementPowerTail p N ζ) ∧
      (∑' n : ℤ, spectralDisplacementPowerTail p N ζ n) ≤ ∑' n : ℤ, M n := by
  have hn (n : ℤ) : 0 ≤ spectralDisplacementPowerTail p N ζ n := by
    unfold spectralDisplacementPowerTail
    split_ifs <;> positivity
  have ha := hs.of_nonneg_of_le hn hb
  exact ⟨ha,ha.tsum_le_tsum hb hs⟩

/-- A convergent displacement power tail implies global coefficient-space membership. -/
theorem memℓp_displacement_of_summable_tail {p : ℝ≥0∞} (hp : 0 < p.toReal)
    (N : ℕ) (ζ : ℤ → ℂ) (hs : Summable (spectralDisplacementPowerTail p N ζ)) :
    Memℓp (fun n : ℤ => ζ n-(Real.pi : ℂ)*n) p := by
  have hf : (fun n : ℤ => if N ≤ n.natAbs then (0 : ℝ) else ‖ζ n-(Real.pi : ℂ)*n‖^p.toReal).HasFiniteSupport := by
    apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
    intro n hn
    have hh : ¬N ≤ n.natAbs := by
      intro h
      simp [Function.mem_support, h] at hn
    constructor <;> omega
  apply (memℓp_gen_iff hp).mpr
  have hsum := hs.add (summable_of_hasFiniteSupport hf)
  convert hsum using 1
  funext n
  simp only [spectralDisplacementPowerTail]
  split_ifs <;> simp

end NLS.ZakharovShabat
