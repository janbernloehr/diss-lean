import NLS.ZakharovShabat.SourceCriticalRootGapNeighborhood

/-!
# Transverse lower bound for the selected standard root

For a horizontal approach to a real gap, the root denominator is at
least the ordinary inverse-square-root boundary denominator. The
estimate is uniform in the transverse height and remains valid near
both branch-point endpoints.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Moving a nonzero distance off a real gap cannot make its standard
root smaller than the boundary square-root weight at the same signed
longitudinal coordinate. -/
theorem normalizedStandardRoot_transverse_norm_lower_bound
    (τ δ t y : ℝ) (hδ : 0 ≤ δ)
    (ht : t ∈ Icc (-1) 1) (hy : y ≠ 0) :
    δ * Real.sqrt (1-t^2) ≤
      ‖normalizedStandardRoot (τ:ℂ) (4*(δ:ℂ)^2)
        (((τ+δ*t:ℝ):ℂ)+(y:ℂ)*I)‖ := by
  let z : ℂ := ((τ+δ*t:ℝ):ℂ)+(y:ℂ)*I
  let R : ℂ := normalizedStandardRoot (τ:ℂ) (4*(δ:ℂ)^2) z
  have hzim : z.im = y := by simp [z]
  have hzt : (τ:ℂ) ≠ z := by
    intro he
    have hz0 : z.im = 0 := by rw [← he]; simp
    exact hy (by linarith)
  have hs : R^2 = ((τ:ℂ)-z)^2-(δ:ℂ)^2 := by
    dsimp [R]
    rw [normalizedStandardRoot_sq _ _ _ hzt]
    ring
  have hre : (R^2).re = -(δ^2*(1-t^2)+y^2) := by
    rw [hs]
    dsimp [z]
    ring_nf
    norm_cast
    simp [Complex.I_sq, Complex.mul_re]
    norm_cast
    ring
  have hrad : 0 ≤ 1-t^2 := by
    have h₁ : 0 ≤ 1+t := by linarith [ht.1]
    have h₂ : 0 ≤ 1-t := by linarith [ht.2]
    nlinarith [mul_nonneg h₁ h₂]
  have hsum : 0 ≤ δ^2*(1-t^2)+y^2 := by positivity
  have hnormsq : δ^2*(1-t^2) ≤ ‖R‖^2 := by
    calc
      δ^2*(1-t^2) ≤ δ^2*(1-t^2)+y^2 := by nlinarith [sq_nonneg y]
      _ = |(R^2).re| := by rw [hre, abs_neg, abs_of_nonneg hsum]
      _ ≤ ‖R^2‖ := Complex.abs_re_le_norm _
      _ = ‖R‖^2 := by rw [norm_pow]
  have htarget : (δ*Real.sqrt (1-t^2))^2 = δ^2*(1-t^2) := by
    rw [mul_pow, Real.sq_sqrt hrad]
  have htarget_nonneg : 0 ≤ δ*Real.sqrt (1-t^2) :=
    mul_nonneg hδ (Real.sqrt_nonneg _)
  change δ*Real.sqrt (1-t^2) ≤ ‖R‖
  nlinarith [norm_nonneg R]

/-- The actual source standard root satisfies the same transverse
estimate when its periodic gap has real endpoints. -/
theorem sourceStandardRoot_transverse_norm_lower_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (t y : ℝ) (ht : t ∈ Icc (-1) 1) (hy : y ≠ 0) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    (b-a)/2 * Real.sqrt (1-t^2) ≤
      ‖sourceStandardRoot hp hp1 ψ n
        (sourceCanonicalRootGapPoint hp hp1 ψ n t+(y:ℂ)*I)‖ := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let τ : ℝ := (a+b)/2
  let δ : ℝ := (b-a)/2
  have hδpos : 0 ≤ δ := by
    change a < b at hopen
    dsimp [δ]
    linarith
  have hτ : sourceStandardRootMidpoint hp hp1 ψ n = (τ:ℂ) := by
    have h := sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
      hp hp1 ψ hreal n 0
    change sourceStandardRootMidpoint hp hp1 ψ n +
      sourceStandardRootHalfGap hp hp1 ψ n * (0:ℂ) =
      (((a+b)/2+(b-a)/2*0:ℝ):ℂ) at h
    simpa [τ] using h
  have hhalf : sourceStandardRootHalfGap hp hp1 ψ n = (δ:ℂ) :=
    sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 ψ hreal n
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n = 2*(δ:ℂ) := by
    have hh := hhalf
    change canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n / 2 = (δ:ℂ) at hh
    calc
      _ = 2*(canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n / 2) := by ring
      _ = 2*(δ:ℂ) := by rw [hh]
  have hpoint : sourceCanonicalRootGapPoint hp hp1 ψ n t =
      (((τ+δ*t:ℝ):ℂ)) := by
    rw [sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
      hp hp1 ψ hreal n t]
    change (((a+b)/2+(b-a)/2*t:ℝ):ℂ) = _
    rfl
  dsimp only
  rw [hpoint]
  change δ*Real.sqrt (1-t^2) ≤
    ‖normalizedStandardRoot
      (sourceStandardRootMidpoint hp hp1 ψ n)
      ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)^2)
      (((τ+δ*t:ℝ):ℂ)+(y:ℂ)*I)‖
  rw [hτ,hgap]
  convert normalizedStandardRoot_transverse_norm_lower_bound
    τ δ t y hδpos ht hy using 1; ring

end NLS.ZakharovShabat
