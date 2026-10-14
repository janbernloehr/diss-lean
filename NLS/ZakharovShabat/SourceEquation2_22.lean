import NLS.ZakharovShabat.SourceGapFunctional
import NLS.ZakharovShabat.SourceTheorem12_1Functions

/-! # The simultaneous psi family solves equation (2.22) on original circuits -/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The family in Theorem 12.1 solves every scalar equation on every original circuit. -/
theorem SourceTheorem12_1Data.equation_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hψV : ψ ∈ V) (n m : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D m \ sourcePeriodicSegment hp hp1 ψ m)) :
    sourceGapFunctional hp hp1 n m ψ Γ (fun z => sourcePsiCandidate n (z,(s n ψ : Coeff p))) = 0 := by
  have he : sourceGapFunctional hp hp1 n m ψ Γ
      (fun z => sourcePsiCandidate n (z,(s n ψ : Coeff p))) =
      ((n-m:ℤ):ℂ)*(2*Real.pi:ℂ)*sourcePsiCircuit hp hp1 n (s n ψ : Coeff p) ψ Γ := by
    unfold sourceGapFunctional sourcePsiCircuit
    have hπ : (2*Real.pi:ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
  rw [he,H.circuit_winding hD ψ hψ hψV n m Γ hΓ]
  by_cases hmn : m = n
  · subst m; simp
  · simp [hmn]


end NLS.ZakharovShabat
