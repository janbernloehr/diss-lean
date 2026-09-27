import NLS.ZakharovShabat.SourceNormalizedActionModel
import NLS.ZakharovShabat.SourceCriticalGapQuotientUniform

/-!
# Bounds for the normalized action cosine error

The exact cosine representation of the normalized action reduces the
estimate in Theorem 11.2 to two quantities: the normalized critical
offset and the distance of the complementary spectral factor from one.
This file makes that reduction quantitative on open real-type gaps.
-/

noncomputable section
open Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A uniform error in the complementary factor controls the cosine
model error. The estimate holds for complex critical offsets. -/
theorem norm_normalizedActionCosineModel_sub_le
    (u : ℂ) (χ : ℝ → ℂ)
    (hχ : IntervalIntegrable χ volume 0 Real.pi)
    (ε : ℝ)
    (hbound : ∀ θ : ℝ, ‖χ θ - 1‖ ≤ ε) :
    ‖normalizedActionCosineModel u χ - (1 + 2*u^2)‖ ≤
      2 * (‖u‖ + 1)^2 * ε := by
  have hpoint (θ : ℝ) :
      ‖(u - (Real.cos θ:ℂ))^2 * (χ θ - 1)‖ ≤
        (‖u‖ + 1)^2 * ε := by
    have hcos : ‖(Real.cos θ:ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one θ
    have hu : ‖u - (Real.cos θ:ℂ)‖ ≤ ‖u‖ + 1 :=
      (norm_sub_le u (Real.cos θ:ℂ)).trans
        (by linarith)
    have hsq : ‖u - (Real.cos θ:ℂ)‖^2 ≤ (‖u‖ + 1)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hu _
    calc
      ‖(u - (Real.cos θ:ℂ))^2 * (χ θ - 1)‖ =
          ‖u - (Real.cos θ:ℂ)‖^2 * ‖χ θ - 1‖ := by
            simp [norm_pow]
      _ ≤ (‖u‖ + 1)^2 * ‖χ θ - 1‖ :=
          mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
      _ ≤ (‖u‖ + 1)^2 * ε :=
          mul_le_mul_of_nonneg_left (hbound θ) (sq_nonneg _)
  have hInt :
      ‖∫ θ in (0:ℝ)..Real.pi,
        (u - (Real.cos θ:ℂ))^2 * (χ θ - 1)‖ ≤
          ((‖u‖ + 1)^2 * ε) * Real.pi := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := Real.pi)
      (C := (‖u‖ + 1)^2 * ε)
      (fun θ _ => hpoint θ)
    simpa [abs_of_pos Real.pi_pos] using h
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcoef : ‖(2/(Real.pi:ℂ))‖ = 2/Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  have hdecomp := normalizedActionCosineModel_eq_one_add_error u χ hχ
  calc
    ‖normalizedActionCosineModel u χ - (1 + 2*u^2)‖ =
        ‖(2/(Real.pi:ℂ)) *
          ∫ θ in (0:ℝ)..Real.pi,
            (u - (Real.cos θ:ℂ))^2 * (χ θ - 1)‖ := by
              rw [hdecomp]
              ring
    _ = (2/Real.pi) *
        ‖∫ θ in (0:ℝ)..Real.pi,
          (u - (Real.cos θ:ℂ))^2 * (χ θ - 1)‖ := by
            rw [norm_mul,hcoef]
    _ ≤ (2/Real.pi) * (((‖u‖ + 1)^2 * ε) * Real.pi) :=
      mul_le_mul_of_nonneg_left hInt (div_nonneg (by norm_num) Real.pi_pos.le)
    _ = 2 * (‖u‖ + 1)^2 * ε := by
      field_simp

/-- On an open real-type gap, the normalized critical-point offset is
twice the gap length times the squared-gap quotient of Lemma 10.10. -/
theorem sourceCriticalNormalizedOffset_eq_two_gap_mul_quotient
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n ≠ 0) :
    (canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n -
      sourceStandardRootMidpoint hp hp1 ψ n) /
        sourceStandardRootHalfGap hp hp1 ψ n =
      2 * sourcePeriodicGapDisplacement hp hp1 ψ n *
        sourceCriticalGapQuotient hp hp1 ψ n := by
  obtain ⟨W,_,_,hWreal,hdata⟩ :=
    exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  have hoffset := (hdata ψ (hWreal hreal) n).2
  have hδ : sourceStandardRootHalfGap hp hp1 ψ n =
      sourcePeriodicGapDisplacement hp hp1 ψ n / 2 := by
    simp only [sourceStandardRootHalfGap,sourcePeriodicGapDisplacement_apply]
  have hδne : sourceStandardRootHalfGap hp hp1 ψ n ≠ 0 := by
    rw [hδ]
    exact div_ne_zero hgap (by norm_num)
  change (canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n -
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n) /
      sourceStandardRootHalfGap hp hp1 ψ n = _
  rw [hoffset, hδ, sourceCriticalGapQuotient_apply]
  field_simp [hgap]

/-- A uniform bound on the complementary spectral factor along the
gap bounds the actual normalized action after its explicit critical
offset term is removed. -/
theorem norm_sourceRawNormalizedAction_sub_criticalTerm_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (ε : ℝ)
    (hfactor : ∀ θ : ℝ,
      ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) - 1‖ ≤ ε) :
    let τ := sourceStandardRootMidpoint hp hp1 ψ n
    let δ := sourceStandardRootHalfGap hp hp1 ψ n
    let crit := canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ‖4 * sourceRawNormalizedAction hp hp1 n ψ -
      (1 + 2*((crit-τ)/δ)^2)‖ ≤
        2 * (‖(crit-τ)/δ‖ + 1)^2 * ε := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let crit := canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let χ : ℝ → ℂ := fun θ =>
    I * sourceCriticalRootRatioExtension hp hp1 n ψ
      (τ+δ*(Real.cos θ:ℂ))
  have hχ : IntervalIntegrable χ volume 0 Real.pi :=
    (sourceCriticalRootRatioExtension_cosine_continuous
      hp hp1 ψ hreal n).intervalIntegrable _ _
  rw [sourceRawNormalizedAction_eq_cosineModel_of_openRealGap
    hp hp1 ψ hreal n hopen]
  exact norm_normalizedActionCosineModel_sub_le
    ((crit-τ)/δ) χ hχ ε hfactor

/-- The normalized action's deviation from one is controlled by the
gap, the critical squared-gap quotient, and the complementary-factor
error on an open real-type gap. -/
theorem norm_sourceRawNormalizedAction_sub_one_le_of_factor_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (ε : ℝ)
    (hfactor : ∀ θ : ℝ,
      ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) - 1‖ ≤ ε) :
    ‖4 * sourceRawNormalizedAction hp hp1 n ψ - 1‖ ≤
      8 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 *
        ‖sourceCriticalGapQuotient hp hp1 ψ n‖^2 +
      2 * (2 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ *
        ‖sourceCriticalGapQuotient hp hp1 ψ n‖ + 1)^2 * ε := by
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ n
  let B := sourceCriticalGapQuotient hp hp1 ψ n
  let u := (canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n -
      sourceStandardRootMidpoint hp hp1 ψ n) /
        sourceStandardRootHalfGap hp hp1 ψ n
  have hgap : γ ≠ 0 := by
    simpa only [γ,sourcePeriodicGapDisplacement_apply] using
      sourceCanonicalPeriodicGap_ne_zero_of_openRealGap
        hp hp1 ψ hreal n hopen
  have hu : u = 2*γ*B :=
    sourceCriticalNormalizedOffset_eq_two_gap_mul_quotient
      hp hp1 ψ hreal n hgap
  have huNorm : ‖u‖ = 2*‖γ‖*‖B‖ := by
    rw [hu]
    simp
  have hmain := norm_sourceRawNormalizedAction_sub_criticalTerm_le
    hp hp1 ψ hreal n hopen ε hfactor
  change ‖4 * sourceRawNormalizedAction hp hp1 n ψ -
      (1+2*u^2)‖ ≤ 2*(‖u‖+1)^2*ε at hmain
  have heq : 4 * sourceRawNormalizedAction hp hp1 n ψ - 1 =
      (4 * sourceRawNormalizedAction hp hp1 n ψ - (1+2*u^2)) +
        2*u^2 := by ring
  rw [heq]
  calc
    ‖(4 * sourceRawNormalizedAction hp hp1 n ψ - (1+2*u^2)) +
        2*u^2‖ ≤
      ‖4 * sourceRawNormalizedAction hp hp1 n ψ - (1+2*u^2)‖ +
        ‖2*u^2‖ := norm_add_le _ _
    _ ≤ 2*(‖u‖+1)^2*ε + 2*‖u‖^2 := by
      simpa [norm_mul,norm_pow] using hmain
    _ = 8*‖γ‖^2*‖B‖^2 + 2*(2*‖γ‖*‖B‖+1)^2*ε := by
      rw [huNorm]
      ring

end NLS.ZakharovShabat
