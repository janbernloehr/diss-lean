import NLS.ZakharovShabat.SourceNormalizedActionEstimate
import NLS.ZakharovShabat.SourceCriticalGapQuotientContinuity

/-!
# Quantitative normalized-action limit at a collapsing real gap

Formula (2.19) has a finite limit when the normalized critical offset
vanishes and the complementary factor approaches its value at the
collapsed midpoint. The estimates below separate those two effects.
They apply directly to the source action on every open real-type gap,
without assigning a value to the raw quotient at a collapsed gap.
-/

noncomputable section
open Complex MeasureTheory intervalIntegral Filter
open scoped ENNReal Topology
namespace NLS.ZakharovShabat

/-- The cosine model with a constant complementary factor is its
universal moment multiplied by that factor. -/
theorem normalizedActionCosineModel_const (u c : ℂ) :
    normalizedActionCosineModel u (fun _ => c) = (1 + 2*u^2)*c := by
  simp only [normalizedActionCosineModel, intervalIntegral.integral_mul_const]
  rw [integral_shifted_cos_sq_complex]
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- Subtracting a constant factor leaves exactly the weighted cosine
integral of the factor error. -/
theorem normalizedActionCosineModel_eq_const_add_error
    (u c : ℂ) (χ : ℝ → ℂ)
    (hχ : IntervalIntegrable χ volume 0 Real.pi) :
    normalizedActionCosineModel u χ =
      (1 + 2*u^2)*c + (2/(Real.pi:ℂ)) *
        ∫ θ in (0:ℝ)..Real.pi,
          (u - (Real.cos θ:ℂ))^2 * (χ θ - c) := by
  have hweight : IntervalIntegrable
      (fun θ : ℝ => (u - (Real.cos θ:ℂ))^2) volume 0 Real.pi := by
    exact (by fun_prop : Continuous (fun θ : ℝ =>
      (u - (Real.cos θ:ℂ))^2)).intervalIntegrable _ _
  have herr : IntervalIntegrable
      (fun θ : ℝ => (u - (Real.cos θ:ℂ))^2 * (χ θ - c))
      volume 0 Real.pi :=
    (hχ.sub ((by fun_prop : Continuous (fun _ : ℝ => c)).intervalIntegrable _ _))
      |>.continuousOn_mul
        ((by fun_prop : Continuous (fun θ : ℝ =>
          (u - (Real.cos θ:ℂ))^2)).continuousOn)
  have hconst : IntervalIntegrable
      (fun θ : ℝ => (u - (Real.cos θ:ℂ))^2 * c)
      volume 0 Real.pi := hweight.mul_const c
  have hpoint (θ : ℝ) :
      (u - (Real.cos θ:ℂ))^2 * χ θ =
        (u - (Real.cos θ:ℂ))^2 * c +
          (u - (Real.cos θ:ℂ))^2 * (χ θ - c) := by ring
  simp only [normalizedActionCosineModel]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add hconst herr,
    intervalIntegral.integral_mul_const,
    integral_shifted_cos_sq_complex]
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- A uniform factor error controls the cosine model relative to the
constant-factor moment. -/
theorem norm_normalizedActionCosineModel_sub_const_moment_le
    (u c : ℂ) (χ : ℝ → ℂ)
    (hχ : IntervalIntegrable χ volume 0 Real.pi)
    (ε : ℝ) (hbound : ∀ θ : ℝ, ‖χ θ - c‖ ≤ ε) :
    ‖normalizedActionCosineModel u χ - (1 + 2*u^2)*c‖ ≤
      2 * (‖u‖ + 1)^2 * ε := by
  have hpoint (θ : ℝ) :
      ‖(u - (Real.cos θ:ℂ))^2 * (χ θ - c)‖ ≤
        (‖u‖ + 1)^2 * ε := by
    have hcos : ‖(Real.cos θ:ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one θ
    have hu : ‖u - (Real.cos θ:ℂ)‖ ≤ ‖u‖ + 1 :=
      (norm_sub_le u (Real.cos θ:ℂ)).trans (by linarith)
    have hsq : ‖u - (Real.cos θ:ℂ)‖^2 ≤ (‖u‖ + 1)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hu _
    calc
      ‖(u - (Real.cos θ:ℂ))^2 * (χ θ - c)‖ =
          ‖u - (Real.cos θ:ℂ)‖^2 * ‖χ θ - c‖ := by
            simp [norm_pow]
      _ ≤ (‖u‖ + 1)^2 * ‖χ θ - c‖ :=
          mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
      _ ≤ (‖u‖ + 1)^2 * ε :=
          mul_le_mul_of_nonneg_left (hbound θ) (sq_nonneg _)
  have hInt :
      ‖∫ θ in (0:ℝ)..Real.pi,
        (u - (Real.cos θ:ℂ))^2 * (χ θ - c)‖ ≤
          ((‖u‖ + 1)^2 * ε) * Real.pi := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := Real.pi)
      (C := (‖u‖ + 1)^2 * ε) (fun θ _ => hpoint θ)
    simpa [abs_of_pos Real.pi_pos] using h
  have hcoef : ‖(2/(Real.pi:ℂ))‖ = 2/Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  have hdecomp := normalizedActionCosineModel_eq_const_add_error u c χ hχ
  calc
    ‖normalizedActionCosineModel u χ - (1 + 2*u^2)*c‖ =
        ‖(2/(Real.pi:ℂ)) *
          ∫ θ in (0:ℝ)..Real.pi,
            (u - (Real.cos θ:ℂ))^2 * (χ θ - c)‖ := by
              rw [hdecomp]
              ring
    _ = (2/Real.pi) *
        ‖∫ θ in (0:ℝ)..Real.pi,
          (u - (Real.cos θ:ℂ))^2 * (χ θ - c)‖ := by
            rw [norm_mul,hcoef]
    _ ≤ (2/Real.pi) * (((‖u‖ + 1)^2 * ε) * Real.pi) :=
      mul_le_mul_of_nonneg_left hInt (div_nonneg (by norm_num) Real.pi_pos.le)
    _ = 2 * (‖u‖ + 1)^2 * ε := by field_simp

/-- When the normalized critical offset tends to zero, the cosine
model approaches the midpoint value of its complementary factor. -/
theorem norm_normalizedActionCosineModel_sub_limitFactor_le
    (u c : ℂ) (χ : ℝ → ℂ)
    (hχ : IntervalIntegrable χ volume 0 Real.pi)
    (ε : ℝ) (hbound : ∀ θ : ℝ, ‖χ θ - c‖ ≤ ε) :
    ‖normalizedActionCosineModel u χ - c‖ ≤
      2 * (‖u‖ + 1)^2 * ε + 2 * ‖u‖^2 * ‖c‖ := by
  have hmain := norm_normalizedActionCosineModel_sub_const_moment_le
    u c χ hχ ε hbound
  have heq : normalizedActionCosineModel u χ - c =
      (normalizedActionCosineModel u χ - (1 + 2*u^2)*c) +
        (2*u^2)*c := by ring
  rw [heq]
  calc
    ‖(normalizedActionCosineModel u χ - (1 + 2*u^2)*c) +
        (2*u^2)*c‖ ≤
      ‖normalizedActionCosineModel u χ - (1 + 2*u^2)*c‖ +
        ‖(2*u^2)*c‖ := norm_add_le _ _
    _ ≤ 2 * (‖u‖ + 1)^2 * ε + 2 * ‖u‖^2 * ‖c‖ := by
      simpa [norm_mul,norm_pow] using
        add_le_add_right hmain (2 * ‖u‖^2 * ‖c‖)

/-- The concrete open-gap action obeys the collapsed-gap limit
estimate. Here `c` can be the complementary spectral factor evaluated
at a collapsed midpoint; the remaining source argument is to control
the factor uniformly along the shrinking cosine path. -/
theorem norm_sourceRawNormalizedAction_sub_limitFactor_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (c : ℂ) (ε : ℝ)
    (hfactor : ∀ θ : ℝ,
      ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) - c‖ ≤ ε) :
    ‖4 * sourceRawNormalizedAction hp hp1 n ψ - c‖ ≤
      2 * (2 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ *
        ‖sourceCriticalGapQuotient hp hp1 ψ n‖ + 1)^2 * ε +
      8 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 *
        ‖sourceCriticalGapQuotient hp hp1 ψ n‖^2 * ‖c‖ := by
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ n
  let B := sourceCriticalGapQuotient hp hp1 ψ n
  let u := (canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n -
      sourceStandardRootMidpoint hp hp1 ψ n) /
        sourceStandardRootHalfGap hp hp1 ψ n
  let χ : ℝ → ℂ := fun θ =>
    I * sourceCriticalRootRatioExtension hp hp1 n ψ
      (sourceStandardRootMidpoint hp hp1 ψ n +
        sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ))
  have hgap : γ ≠ 0 := by
    simpa only [γ,sourcePeriodicGapDisplacement_apply] using
      sourceCanonicalPeriodicGap_ne_zero_of_openRealGap
        hp hp1 ψ hreal n hopen
  have hu : u = 2*γ*B :=
    sourceCriticalNormalizedOffset_eq_two_gap_mul_quotient
      hp hp1 ψ hreal n hgap
  have huNorm : ‖u‖ = 2*‖γ‖*‖B‖ := by rw [hu]; simp
  have hχ : IntervalIntegrable χ volume 0 Real.pi :=
    (sourceCriticalRootRatioExtension_cosine_continuous
      hp hp1 ψ hreal n).intervalIntegrable _ _
  have hmodel := sourceRawNormalizedAction_eq_cosineModel_of_openRealGap
    hp hp1 ψ hreal n hopen
  change 4 * sourceRawNormalizedAction hp hp1 n ψ =
    normalizedActionCosineModel u χ at hmodel
  rw [hmodel]
  have hbound : ∀ θ : ℝ, ‖χ θ - c‖ ≤ ε := hfactor
  exact (norm_normalizedActionCosineModel_sub_limitFactor_le
    u c χ hχ ε hbound).trans_eq (by rw [huNorm]; ring)

/-- Formula (2.19) gives the asserted collapsed-gap limit along any
family of open real-type gaps for which the normalized critical offset
vanishes and the complementary factor converges uniformly on the
cosine path. -/
theorem sourceRawNormalizedAction_tendsto_limitFactor_of_uniform_factor
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (F : Filter (CoeffPair p)) (c : ℂ)
    (ε : CoeffPair p → ℝ)
    (hopen : ∀ᶠ ψ in F,
      IsRealType (CoeffPair.toMax p ψ) ∧
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re <
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re)
    (hfactor : ∀ᶠ ψ in F, ∀ θ : ℝ,
      ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) - c‖ ≤ ε ψ)
    (hsmall : Tendsto (fun ψ : CoeffPair p =>
      ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ *
        ‖sourceCriticalGapQuotient hp hp1 ψ n‖) F (𝓝 0))
    (hε : Tendsto ε F (𝓝 0)) :
    Tendsto (fun ψ : CoeffPair p =>
      4 * sourceRawNormalizedAction hp hp1 n ψ) F (𝓝 c) := by
  let r (ψ : CoeffPair p) :=
    ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ *
      ‖sourceCriticalGapQuotient hp hp1 ψ n‖
  have hr : Tendsto r F (𝓝 0) := hsmall
  have hcont : ContinuousAt (fun x : ℝ × ℝ =>
      2 * (2*x.1+1)^2*x.2 + 8*x.1^2*‖c‖) (0,0) := by fun_prop
  have hpair : Tendsto (fun ψ : CoeffPair p => (r ψ, ε ψ)) F
      (𝓝 ((0:ℝ),(0:ℝ))) := by
    simpa only [nhds_prod_eq] using hr.prodMk hε
  have hmajorLimit : Tendsto (fun ψ : CoeffPair p =>
      2 * (2*r ψ+1)^2*ε ψ + 8*(r ψ)^2*‖c‖) F (𝓝 0) := by
    change Tendsto ((fun x : ℝ × ℝ =>
      2 * (2*x.1+1)^2*x.2 + 8*x.1^2*‖c‖) ∘
        (fun ψ : CoeffPair p => (r ψ, ε ψ))) F (𝓝 0)
    simpa using hcont.tendsto.comp hpair
  have hmajor : ∀ᶠ ψ in F,
      ‖4 * sourceRawNormalizedAction hp hp1 n ψ-c‖ ≤
        2 * (2*r ψ+1)^2*ε ψ + 8*(r ψ)^2*‖c‖ := by
    filter_upwards [hopen,hfactor] with ψ hψ hf
    have h := norm_sourceRawNormalizedAction_sub_limitFactor_le
      hp hp1 ψ hψ.1 n hψ.2 c (ε ψ) hf
    simpa only [r, mul_pow, mul_assoc] using h
  have hnorm : Tendsto (fun ψ : CoeffPair p =>
      ‖4 * sourceRawNormalizedAction hp hp1 n ψ-c‖) F (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      hmajor hmajorLimit
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- At a collapsed real-type gap, the normalized critical offset in
(2.19) tends to zero along every source family approaching the base
potential. The squared-gap critical quotient is continuous there. -/
theorem sourceCriticalNormalizedOffset_tendsto_zero_of_collapsedGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0)
    (F : Filter (CoeffPair p)) (hφ : Tendsto id F (𝓝 φ)) :
    Tendsto (fun ψ : CoeffPair p =>
      ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ *
        ‖sourceCriticalGapQuotient hp hp1 ψ n‖) F (𝓝 0) := by
  have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType
    hp hp1 φ hreal n
  have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType
    hp hp1 φ hreal n
  have hγ : ContinuousAt (fun ψ : CoeffPair p =>
      sourcePeriodicGapDisplacement hp hp1 ψ n) φ := by
    simp only [sourcePeriodicGapDisplacement_apply, canonicalPeriodicGap]
    exact hR.sub hL
  have hB : ContinuousAt (fun ψ : CoeffPair p =>
      sourceCriticalGapQuotient hp hp1 ψ n) φ := by
    simpa only [sourceCriticalGapQuotient_apply] using
      (continuousAt_sourceCriticalGapQuotient_of_realType
        hp hp1 φ hreal n)
  have hprod : ContinuousAt (fun ψ : CoeffPair p =>
      sourcePeriodicGapDisplacement hp hp1 ψ n *
        sourceCriticalGapQuotient hp hp1 ψ n) φ := hγ.mul hB
  have hzero : Tendsto (fun ψ : CoeffPair p =>
      sourcePeriodicGapDisplacement hp hp1 ψ n *
        sourceCriticalGapQuotient hp hp1 ψ n) F (𝓝 0) := by
    have hbase : sourcePeriodicGapDisplacement hp hp1 φ n *
        sourceCriticalGapQuotient hp hp1 φ n = 0 := by rw [hgap]; simp
    have hlim := hprod.tendsto.comp hφ
    rw [hbase] at hlim
    exact hlim
  simpa only [norm_mul,norm_zero] using hzero.norm

/-- The remaining analytic input for the collapsed-gap limit is the
uniform continuity of the deleted factor along the shrinking cosine
path. Given that input, the open-gap quotient approaches precisely
one quarter of the factor at the collapsed midpoint. -/
theorem sourceRawNormalizedAction_tendsto_collapsedFactor
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0)
    (F : Filter (CoeffPair p)) (hφ : Tendsto id F (𝓝 φ))
    (hopen : ∀ᶠ ψ in F,
      IsRealType (CoeffPair.toMax p ψ) ∧
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re <
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re)
    (ε : CoeffPair p → ℝ) (hε : Tendsto ε F (𝓝 0))
    (hfactor : ∀ᶠ ψ in F, ∀ θ : ℝ,
      ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) -
        I * sourceCriticalRootRatioExtension hp hp1 n φ
          (sourceStandardRootMidpoint hp hp1 φ n)‖ ≤ ε ψ) :
    Tendsto (fun ψ : CoeffPair p =>
      4 * sourceRawNormalizedAction hp hp1 n ψ) F
      (𝓝 (I * sourceCriticalRootRatioExtension hp hp1 n φ
        (sourceStandardRootMidpoint hp hp1 φ n))) := by
  exact sourceRawNormalizedAction_tendsto_limitFactor_of_uniform_factor
    hp hp1 n F _ ε hopen hfactor
      (sourceCriticalNormalizedOffset_tendsto_zero_of_collapsedGap
        hp hp1 n φ hreal hgap F hφ) hε

/-- The value prescribed by the collapsed cosine moment for the
normalized action. Proving continuity of the deleted factor in the
source parameter will identify it as the removable quotient value. -/
def sourceNormalizedActionCollapsedCandidate
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) : ℂ :=
  I * sourceCriticalRootRatioExtension hp hp1 n φ
    (sourceStandardRootMidpoint hp hp1 φ n) / 4

/-- Under uniform spectral-factor convergence, the raw normalized
action tends to the explicit collapsed candidate. -/
theorem sourceRawNormalizedAction_tendsto_collapsedCandidate
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0)
    (F : Filter (CoeffPair p)) (hφ : Tendsto id F (𝓝 φ))
    (hopen : ∀ᶠ ψ in F,
      IsRealType (CoeffPair.toMax p ψ) ∧
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re <
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re)
    (ε : CoeffPair p → ℝ) (hε : Tendsto ε F (𝓝 0))
    (hfactor : ∀ᶠ ψ in F, ∀ θ : ℝ,
      ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) -
        I * sourceCriticalRootRatioExtension hp hp1 n φ
          (sourceStandardRootMidpoint hp hp1 φ n)‖ ≤ ε ψ) :
    Tendsto (sourceRawNormalizedAction hp hp1 n) F
      (𝓝 (sourceNormalizedActionCollapsedCandidate hp hp1 n φ)) := by
  have h := sourceRawNormalizedAction_tendsto_collapsedFactor
    hp hp1 n φ hreal hgap F hφ hopen ε hε hfactor
  have hscaled := h.div_const (4:ℂ)
  have hfun : (fun ψ : CoeffPair p =>
      4 * sourceRawNormalizedAction hp hp1 n ψ / 4) =
        sourceRawNormalizedAction hp hp1 n := by
    funext ψ
    apply (div_eq_iff (by norm_num : (4:ℂ) ≠ 0)).2
    ring
  rw [hfun] at hscaled
  exact hscaled

end NLS.ZakharovShabat
