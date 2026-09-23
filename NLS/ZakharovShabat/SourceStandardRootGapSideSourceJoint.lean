import NLS.ZakharovShabat.SourceStandardRootGapSideJoint

/- Joint boundary values of the canonical source root on the open sides of a
   noncollapsed periodic gap. These strengthen the transverse-path version of
   equation (2.12) by allowing the spectral parameter to move freely in each
   side as it approaches any gap point. -/

noncomputable section
open Complex Filter
open scoped Topology ENNReal

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equation (2.12) for arbitrary approach from the upper side of a canonical
    source periodic gap, including its midpoint and endpoints. -/
theorem sourceStandardRoot_tendsto_gap_upper_side (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (sourceStandardRoot hp hp1 ψ n)
      (𝓝[standardRootGapUpperSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (t:ℂ)))
      (𝓝 (-sourceStandardRootHalfGap hp hp1 ψ n * I *
        (Real.sqrt (1-t^2):ℂ))) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hδ : δ ≠ 0 := by
    dsimp [δ, sourceStandardRootHalfGap]
    exact div_ne_zero hgap (by norm_num)
  have h := normalizedStandardRoot_tendsto_gap_upper_side τ δ t hδ htl htr
  have hg : (2*δ)^2 =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)^2 := by
    dsimp [δ, sourceStandardRootHalfGap]
    ring
  convert h using 1
  · ext z
    unfold sourceStandardRoot
    change normalizedStandardRoot τ
      ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)^2) z =
      normalizedStandardRoot τ ((2*δ)^2) z
    rw [hg]

/-- Equation (2.12) for arbitrary approach from the lower side of a canonical
    source periodic gap, including its midpoint and endpoints. -/
theorem sourceStandardRoot_tendsto_gap_lower_side (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (t : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (sourceStandardRoot hp hp1 ψ n)
      (𝓝[standardRootGapLowerSide
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)]
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (t:ℂ)))
      (𝓝 (sourceStandardRootHalfGap hp hp1 ψ n * I *
        (Real.sqrt (1-t^2):ℂ))) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hδ : δ ≠ 0 := by
    dsimp [δ, sourceStandardRootHalfGap]
    exact div_ne_zero hgap (by norm_num)
  have h := normalizedStandardRoot_tendsto_gap_lower_side τ δ t hδ htl htr
  have hg : (2*δ)^2 =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)^2 := by
    dsimp [δ, sourceStandardRootHalfGap]
    ring
  convert h using 1
  · ext z
    unfold sourceStandardRoot
    change normalizedStandardRoot τ
      ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)^2) z =
      normalizedStandardRoot τ ((2*δ)^2) z
    rw [hg]

end NLS.ZakharovShabat
