import NLS.ZakharovShabat.SourceNormalizedActionComplexExtension
import NLS.ZakharovShabat.SourceNormalizedActionExtensionTailBound
import NLS.ZakharovShabat.SourceNormalizedActionSequenceMajorants

/-!
# Sequence majorants across collapsed real-type gaps

The factor estimate on the cosine path does not require an open gap.
At a collapsed gap the normalized action is its midpoint value, so the
same `ℓq + ℓ^(p/2)` majorants control the continuous extension on the
entire real-type locus.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A pointwise factor estimate controls the normalized-action
extension whether the selected real-type gap is open or collapsed. -/
theorem norm_sourceNormalizedActionComplexExtension_sub_one_le_of_factor_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (ε : ℝ)
    (hfactor : ∀ θ : ℝ,
      ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) - 1‖ ≤ ε) :
    ‖4 * sourceNormalizedActionComplexExtension hp hp1 n ψ - 1‖ ≤
      8 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 *
        ‖sourceCriticalGapQuotient hp hp1 ψ n‖^2 +
      2 * (2 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ *
        ‖sourceCriticalGapQuotient hp hp1 ψ n‖ + 1)^2 * ε := by
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · have hmid := hfactor (Real.pi/2)
    have hvalue : 4 * sourceNormalizedActionCollapsedCandidate hp hp1 n ψ =
        I * sourceCriticalRootRatioExtension hp hp1 n ψ
          (sourceStandardRootMidpoint hp hp1 ψ n) := by
      simp only [sourceNormalizedActionCollapsedCandidate]
      ring
    have hbound : ‖4 * sourceNormalizedActionCollapsedCandidate hp hp1 n ψ - 1‖ ≤
        ε := by
      rw [hvalue]
      simpa only [Real.cos_pi_div_two, Complex.ofReal_zero, mul_zero,
        add_zero] using hmid
    have hε : 0 ≤ ε := (norm_nonneg _).trans hbound
    simp only [sourceNormalizedActionComplexExtension,
      sourceNormalizedActionRealExtension, hgap,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul,
      mul_zero, zero_add]
    calc
      ‖4 * sourceNormalizedActionCollapsedCandidate hp hp1 n ψ - 1‖ ≤ ε := hbound
      _ ≤ 2 * 1^2 * ε := by nlinarith
  · have hopen := source_openRealGap_of_realType_gap_ne_zero
      hp hp1 n ψ hreal hgap
    have hbound := norm_sourceRawNormalizedAction_sub_one_le_of_factor_bound
      hp hp1 ψ hreal n hopen ε hfactor
    simpa only [sourceNormalizedActionComplexExtension,
      sourceNormalizedActionRealExtension, if_neg hgap] using hbound

/-- The normalized-action extension majorants are locally uniformly bounded in their
respective sequence norms, including the quasi-Banach exponent
`p/2 < 1`. -/
theorem exists_local_sourceNormalizedActionComplexExtension_uniformSequenceMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
        ∃ Cq : Coeff q, ∃ Cg : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ, K ≤ n.natAbs →
            IsRealType (CoeffPair.toMax p ψ) →
            ‖4 * sourceNormalizedActionComplexExtension hp hp1 n ψ - 1‖ ≤
              ‖Cq n‖ + ‖Cg n‖) ∧
          ‖Cq‖ ≤ Lq ∧ ‖Cg‖ ≤ Lg := by
  obtain ⟨Vf,hVfopen,hφVf,K,Lfq,Lfg,hfactor⟩ :=
    exists_local_sourceNormalizedAction_factor_uniformMajorants
      hp hp1 hq1 hq hhalf φ hφ
  obtain ⟨Vd,hVdopen,hφVd,Ld,hLd0,hD⟩ :=
    exists_local_sourceNormalizedActionCriticalMajorant_bound hp hp1 φ hφ
  obtain ⟨_,_,Vγ,hVγopen,hφVγ,G,hG,hγ⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ
      (by norm_num : (0:ℝ) < 1)
  obtain ⟨Vb,hVbopen,hφVb,T,hT,hB⟩ :=
    exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ hφ
  obtain ⟨Bq₀,Bg₀,_,hBq₀,hBg₀⟩ := hfactor φ hφVf
  have hLfq : 0 ≤ Lfq := (lp.norm_nonneg' Bq₀).trans hBq₀
  have hLfg : 0 ≤ Lfg := (lp.norm_nonneg' Bg₀).trans hBg₀
  let V := ((Vf ∩ Vd) ∩ Vγ) ∩ Vb
  let M₀ : ℝ := 2 * (2*G*T+1)^2
  let Aq : ℝ := M₀*Lfq
  let Ad : ℝ := 8*Ld
  let Ag : ℝ := M₀*Lfg
  let r := ENNReal.ofReal (p.toReal/2)
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hrEq : r.toReal = p.toReal/2 := by
    simp only [r, ENNReal.toReal_ofReal (by positivity : 0 ≤ p.toReal/2)]
  have hr : 0 < r.toReal := by rw [hrEq]; positivity
  have hrENN : 0 < r := ENNReal.ofReal_pos.mpr (by positivity)
  let Lg : ℝ := max (Ad+Ag)
    ((Ad^r.toReal+Ag^r.toReal)^(r.toReal)⁻¹)
  have hM₀ : 0 ≤ M₀ := by dsimp [M₀]; positivity
  refine ⟨V,(((hVfopen.inter hVdopen).inter hVγopen).inter hVbopen),
    ⟨⟨⟨hφVf,hφVd⟩,hφVγ⟩,hφVb⟩,K,Aq,Lg,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ := hfactor ψ hψ.1.1.1
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ
  let B := sourceCriticalGapQuotient hp hp1 ψ
  let M : ℝ := 2*(2*‖γ‖*‖B‖+1)^2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMle : M ≤ M₀ := by
    dsimp [M,M₀]
    gcongr
    · exact (hγ ψ hψ.1.2).1
    · exact (hB ψ hψ.2).1
  let D := sourceNormalizedActionCriticalMajorant hp hp1 ψ
  let Cq : Coeff q := (M:ℂ) • Coeff.magnitude Bq
  let Da : Coeff r := (8:ℂ) • Coeff.magnitude D
  let Gb : Coeff r := (M:ℂ) • Coeff.magnitude Bg
  let Cg : Coeff r := Da + Gb
  have hCqNorm : ‖Cq‖ ≤ Aq := by
    have hn : ‖Cq‖ = M*‖Bq‖ := by
      simp only [Cq, lp.norm_const_smul (zero_lt_one.trans hq1).ne',
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM,
        Coeff.norm_magnitude]
    rw [hn]
    exact mul_le_mul hMle hBq (lp.norm_nonneg' Bq) hM₀
  have hDaNorm : ‖Da‖ ≤ Ad := by
    have hn : ‖Da‖ = 8*‖D‖ := by
      change ‖(8:ℂ) • Coeff.magnitude D‖ = 8*‖D‖
      rw [lp.norm_const_smul hrENN.ne', Coeff.norm_magnitude_quasi hrENN.ne']
      norm_num
    rw [hn]
    exact mul_le_mul_of_nonneg_left (hD ψ hψ.1.1.2) (by norm_num)
  have hGbNorm : ‖Gb‖ ≤ Ag := by
    have hn : ‖Gb‖ = M*‖Bg‖ := by
      change ‖(M:ℂ) • Coeff.magnitude Bg‖ = M*‖Bg‖
      rw [lp.norm_const_smul hrENN.ne', Coeff.norm_magnitude_quasi hrENN.ne']
      simp [Complex.norm_real, Real.norm_eq_abs, hM]
    rw [hn]
    exact mul_le_mul hMle hBg (lp.norm_nonneg' Bg) hM₀
  have hCgNorm : ‖Cg‖ ≤ Lg :=
    Coeff.norm_add_le_uniform hr Da Gb hDaNorm hGbNorm
  refine ⟨Cq,Cg,?_,hCqNorm,hCgNorm⟩
  intro n hn hreal
  have hγn : ‖γ n‖ ≤ ‖γ‖ :=
    lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' γ n
  have hBn : ‖B n‖ ≤ ‖B‖ :=
    lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' B n
  have hfactorN :
      2 * (2 * ‖γ n‖ * ‖B n‖ + 1)^2 ≤ M := by
    dsimp [M]
    gcongr
  have hbound := norm_sourceNormalizedActionComplexExtension_sub_one_le_of_factor_bound
    hp hp1 ψ hreal n (‖Bq n‖+‖Bg n‖) (hpoint n hn)
  change ‖4 * sourceNormalizedActionComplexExtension hp hp1 n ψ - 1‖ ≤
    8 * ‖γ n‖^2 * ‖B n‖^2 +
    2 * (2 * ‖γ n‖ * ‖B n‖ + 1)^2 *
      (‖Bq n‖ + ‖Bg n‖) at hbound
  have hCq : ‖Cq n‖ = M*‖Bq n‖ :=
    norm_smul_magnitude_apply Bq M hM n
  have hCg : ‖Cg n‖ =
      8*‖γ n‖^2*‖B n‖^2 + M*‖Bg n‖ := by
    rw [show ‖Cg n‖ = 8*‖D n‖ + M*‖Bg n‖ from
      norm_add_smul_magnitude_apply D Bg 8 M (by norm_num) hM n]
    simp only [D, norm_sourceNormalizedActionCriticalMajorant_apply, γ, B]
    ring
  rw [hCq,hCg]
  nlinarith [mul_le_mul_of_nonneg_right hfactorN
    (add_nonneg (norm_nonneg (Bq n)) (norm_nonneg (Bg n)))]

/-- The normalized-action extension has an `ℓq + ℓ^(p/2)`
majorant at all sufficiently distant real-type gaps, with no
open-gap assumption. -/
theorem exists_local_sourceNormalizedActionComplexExtension_twoSequenceMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∀ ψ ∈ V,
        ∃ Cq : Coeff q, ∃ Cg : Coeff (ENNReal.ofReal (p.toReal/2)),
          ∀ n : ℤ, K ≤ n.natAbs →
            IsRealType (CoeffPair.toMax p ψ) →
            ‖4 * sourceNormalizedActionComplexExtension hp hp1 n ψ - 1‖ ≤
              ‖Cq n‖ + ‖Cg n‖ := by
  obtain ⟨V,hVopen,hφV,K,Lq,Lg,hmajor⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_uniformSequenceMajorants
      hp hp1 hq1 hq hhalf φ hφ
  refine ⟨V,hVopen,hφV,K,?_⟩
  intro ψ hψ
  obtain ⟨Cq,Cg,hpoint,_,_⟩ := hmajor ψ hψ
  exact ⟨Cq,Cg,hpoint⟩


end NLS.ZakharovShabat
