import NLS.ZakharovShabat.SourceStandardRootGapSideComplex

/-!
# Gap-side values of the canonical source standard root

Equation (2.11) parametrizes the two sides of a noncollapsed complex
periodic gap by its canonical midpoint and half-gap. The affine
complex-gap boundary theorem gives both signs in equation (2.12) for
all `-1 ≤ t ≤ 1`.
-/

noncomputable section
open Complex Filter
open scoped Topology ENNReal

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The midpoint used in the canonical source standard root. -/
abbrev sourceStandardRootMidpoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n

/-- Half of the canonical source periodic gap, used in (2.11). -/
abbrev sourceStandardRootHalfGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n / 2

/-- Upper gap-side value of the canonical source root in (2.12). -/
theorem sourceStandardRoot_tendsto_gap_upper (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (fun ε : ℝ => sourceStandardRoot hp hp1 ψ n
      (sourceStandardRootMidpoint hp hp1 ψ n +
        sourceStandardRootHalfGap hp hp1 ψ n * ((t:ℂ)+(ε:ℂ)*I)))
      (𝓝[>] (0:ℝ))
      (𝓝 (-sourceStandardRootHalfGap hp hp1 ψ n * I *
        (Real.sqrt (1-t^2):ℂ))) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hδ : δ ≠ 0 := by
    dsimp [δ, sourceStandardRootHalfGap]
    exact div_ne_zero hgap (by norm_num)
  have h := normalizedStandardRoot_tendsto_gap_upper_complex τ δ t hδ htl htr
  have hg : (2*δ)^2 =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)^2 := by
    dsimp [δ, sourceStandardRootHalfGap]
    ring
  convert h using 1
  · ext ε
    unfold sourceStandardRoot
    change normalizedStandardRoot τ
      ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)^2)
      (τ+δ*((t:ℂ)+(ε:ℂ)*I)) =
      normalizedStandardRoot τ ((2*δ)^2)
      (τ+δ*((t:ℂ)+(ε:ℂ)*I))
    rw [hg]

/-- Lower gap-side value of the canonical source root in (2.12). -/
theorem sourceStandardRoot_tendsto_gap_lower (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (fun ε : ℝ => sourceStandardRoot hp hp1 ψ n
      (sourceStandardRootMidpoint hp hp1 ψ n +
        sourceStandardRootHalfGap hp hp1 ψ n * ((t:ℂ)-(ε:ℂ)*I)))
      (𝓝[>] (0:ℝ))
      (𝓝 (sourceStandardRootHalfGap hp hp1 ψ n * I *
        (Real.sqrt (1-t^2):ℂ))) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hδ : δ ≠ 0 := by
    dsimp [δ, sourceStandardRootHalfGap]
    exact div_ne_zero hgap (by norm_num)
  have h := normalizedStandardRoot_tendsto_gap_lower_complex τ δ t hδ htl htr
  have hg : (2*δ)^2 =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)^2 := by
    dsimp [δ, sourceStandardRootHalfGap]
    ring
  convert h using 1
  · ext ε
    unfold sourceStandardRoot
    change normalizedStandardRoot τ
      ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)^2)
      (τ+δ*((t:ℂ)-(ε:ℂ)*I)) =
      normalizedStandardRoot τ ((2*δ)^2)
      (τ+δ*((t:ℂ)-(ε:ℂ)*I))
    rw [hg]

end NLS.ZakharovShabat
