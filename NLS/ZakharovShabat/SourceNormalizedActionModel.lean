import NLS.ZakharovShabat.SourceComplexActionZeroLocus
import NLS.ZakharovShabat.SourceRealAction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The leading cosine moment in the normalized action

After the selected gap is parametrized by its midpoint and half-gap,
the principal term of the normalized action in (2.19) is a cosine
moment. Its exact evaluation is the source of the constant `1` in
Theorem 11.2. The spectral complementary factor will enter separately.
-/

noncomputable section
open Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The real second moment of the shifted cosine parameter. -/
theorem integral_shifted_cos_sq (u : ℝ) :
    (∫ θ in (0:ℝ)..Real.pi, (u - Real.cos θ)^2) =
      Real.pi * (u^2 + 1/2) := by
  have hpoint (θ : ℝ) :
      (u - Real.cos θ)^2 =
        u^2 - (2*u)*Real.cos θ + (Real.cos θ)^2 := by
    ring
  simp_rw [hpoint]
  have hconst : IntervalIntegrable (fun _ : ℝ => u^2) volume 0 Real.pi := by
    exact (by fun_prop : Continuous (fun _ : ℝ => u^2)).intervalIntegrable _ _
  have hcos : IntervalIntegrable (fun θ : ℝ => (2*u)*Real.cos θ)
      volume 0 Real.pi := by
    exact (by fun_prop : Continuous (fun θ : ℝ => (2*u)*Real.cos θ)).intervalIntegrable _ _
  have hcos2 : IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ 2)
      volume 0 Real.pi := by
    exact (by fun_prop : Continuous (fun θ : ℝ => Real.cos θ ^ 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hconst.sub hcos) hcos2,
    intervalIntegral.integral_sub hconst hcos]
  simp [intervalIntegral.integral_const_mul, integral_cos_sq,
    Real.sin_pi, Real.sin_zero]
  ring

/-- The same moment with a complex normalized critical-point offset. -/
theorem integral_shifted_cos_sq_complex (u : ℂ) :
    (∫ θ in (0:ℝ)..Real.pi, (u - (Real.cos θ:ℂ))^2) =
      (Real.pi:ℂ) * (u^2 + 1/2) := by
  have hpoint (θ : ℝ) :
      (u - (Real.cos θ:ℂ))^2 =
        u^2 - (2*u)*(Real.cos θ:ℂ) + (Real.cos θ:ℂ)^2 := by
    ring
  simp_rw [hpoint]
  have hconst : IntervalIntegrable (fun _ : ℝ => u^2) volume 0 Real.pi := by
    exact (by fun_prop : Continuous (fun _ : ℝ => u^2)).intervalIntegrable _ _
  have hcos : IntervalIntegrable (fun θ : ℝ => (2*u)*(Real.cos θ:ℂ))
      volume 0 Real.pi := by
    exact (by fun_prop : Continuous (fun θ : ℝ => (2*u)*(Real.cos θ:ℂ))).intervalIntegrable _ _
  have hcos2 : IntervalIntegrable (fun θ : ℝ => (Real.cos θ:ℂ)^2)
      volume 0 Real.pi := by
    exact (by fun_prop : Continuous (fun θ : ℝ => (Real.cos θ:ℂ)^2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hconst.sub hcos) hcos2,
    intervalIntegral.integral_sub hconst hcos]
  simp only [intervalIntegral.integral_const_mul]
  have hcos0 : (∫ θ in (0:ℝ)..Real.pi, (Real.cos θ:ℂ)) = 0 := by
    rw [integral_ofReal]
    simp
  have hcos2val :
      (∫ θ in (0:ℝ)..Real.pi, (Real.cos θ:ℂ)^2) =
        (Real.pi:ℂ)/2 := by
    have hcast : (fun θ : ℝ => (Real.cos θ:ℂ)^2) =
        (fun θ : ℝ => (((Real.cos θ)^2:ℝ):ℂ)) := by
      funext θ
      norm_cast
    rw [hcast, integral_ofReal]
    simp [integral_cos_sq]
  rw [hcos0,hcos2val]
  simp
  ring

/-- The abstract cosine formula for the normalized action, with the
complementary spectral factor supplied as a function of the cosine
parameter. -/
def normalizedActionCosineModel (u : ℂ) (χ : ℝ → ℂ) : ℂ :=
  (2/(Real.pi:ℂ)) *
    ∫ θ in (0:ℝ)..Real.pi,
      (u - (Real.cos θ:ℂ))^2 * χ θ

/-- With complementary factor one, the normalized action model has
the exact leading value `1 + 2u²`. -/
theorem normalizedActionCosineModel_one (u : ℂ) :
    normalizedActionCosineModel u (fun _ => 1) = 1 + 2*u^2 := by
  simp only [normalizedActionCosineModel, mul_one]
  rw [integral_shifted_cos_sq_complex]
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- The exact model separates its universal cosine moment from the
error in the complementary factor. This is the algebraic form used
before estimating the remainder in Theorem 11.2. -/
theorem normalizedActionCosineModel_eq_one_add_error
    (u : ℂ) (χ : ℝ → ℂ)
    (hχ : IntervalIntegrable χ volume 0 Real.pi) :
    normalizedActionCosineModel u χ =
      1 + 2*u^2 + (2/(Real.pi:ℂ)) *
        ∫ θ in (0:ℝ)..Real.pi,
          (u - (Real.cos θ:ℂ))^2 * (χ θ - 1) := by
  have hweight : IntervalIntegrable
      (fun θ : ℝ => (u - (Real.cos θ:ℂ))^2) volume 0 Real.pi := by
    exact (by fun_prop : Continuous (fun θ : ℝ =>
      (u - (Real.cos θ:ℂ))^2)).intervalIntegrable _ _
  have herr : IntervalIntegrable
      (fun θ : ℝ => (u - (Real.cos θ:ℂ))^2 * (χ θ - 1))
      volume 0 Real.pi :=
    (hχ.sub ((by fun_prop : Continuous (fun _ : ℝ => (1:ℂ))).intervalIntegrable _ _))
      |>.continuousOn_mul
        ((by fun_prop : Continuous (fun θ : ℝ =>
          (u - (Real.cos θ:ℂ))^2)).continuousOn)
  have hpoint (θ : ℝ) :
      (u - (Real.cos θ:ℂ))^2 * χ θ =
        (u - (Real.cos θ:ℂ))^2 +
          (u - (Real.cos θ:ℂ))^2 * (χ θ - 1) := by
    ring
  simp only [normalizedActionCosineModel]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add hweight herr,
    integral_shifted_cos_sq_complex]
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- The glued complex action, restricted to an open real-type gap,
equals the weighted upper-side cosine integral. This puts the actual
action into the parametrization used for the normalized model. -/
theorem sourceComplexAction_eq_upper_cosineBoundaryIntegral
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    sourceComplexAction hp hp1 n ψ =
      -(2 * (Real.pi : ℂ)⁻¹) *
        sourceAction_cosineBoundaryIntegral hp hp1 ψ n 0 true := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  let ε₁ := sourceRealActionEpsilon hp hp1 ψ hreal n
  obtain ⟨ε₂,hε₂,hformula⟩ :=
    exists_sourceActionCircle_eq_upperBoundaryIntegral
      hp hp1 ψ hreal n hopen
  have hε₁ : 0 < ε₁ :=
    (sourceRealActionEpsilon_spec hp hp1 ψ hreal n).1
  let η := min ε₁ ε₂ / 2
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hη₁ : η ∈ Set.Ioc 0 ε₁ := by
    constructor
    · exact hη
    · dsimp [η]
      linarith [min_le_left ε₁ ε₂, hε₁]
  have hη₂ : η ∈ Set.Ioc 0 ε₂ := by
    constructor
    · exact hη
    · dsimp [η]
      linarith [min_le_right ε₁ ε₂, hε₂]
  calc
    sourceComplexAction hp hp1 n ψ =
        sourceRealAction hp hp1 ψ hreal n :=
          sourceComplexAction_eq_sourceRealAction hp hp1 n ψ hreal
    _ = sourceActionCircle hp hp1 ψ c (d+η) := by
          exact sourceRealAction_eq_small_midpointCircle
            hp hp1 ψ hreal n hη₁
    _ = -(2 * (Real.pi : ℂ)⁻¹) *
          sourceAction_cosineBoundaryIntegral hp hp1 ψ n 0 true :=
            hformula η hη₂

/-- The upper gap-side action integral is independent of the real
spectral point used to recenter it. The missing term is exactly the
vanishing unweighted critical-root integral. -/
theorem sourceAction_upper_cosineBoundaryIntegral_recenter
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) true =
      sourceAction_cosineBoundaryIntegral hp hp1 ψ n 0 true := by
  rw [sourceAction_cosineBoundaryIntegral_eq_gapSidePathIntegral
      hp hp1 ψ hreal n hopen q true]
  rw [show sourceAction_cosineBoundaryIntegral hp hp1 ψ n 0 true =
      gapSidePathIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)
        (sourceActionGapNumerator hp hp1 ψ n 0) (-1) 1 true from by
      simpa using (sourceAction_cosineBoundaryIntegral_eq_gapSidePathIntegral
        hp hp1 ψ hreal n hopen 0 true)]
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let F := sourceCriticalRootGapNumerator hp hp1 ψ n
  let K (t : ℝ) : ℂ :=
    δ / (-δ*I * (Real.sqrt (1-t^2):ℂ))
  have hF : IntervalIntegrable
      (fun t : ℝ => F (τ+δ*(t:ℂ)) * K t) volume (-1) 1 := by
    exact sourceCriticalRoot_gapSidePathIntegrand_intervalIntegrable
      hp hp1 ψ hreal n hopen true
  have h0 : IntervalIntegrable
      (fun t : ℝ => ((τ+δ*(t:ℂ))-0) * F (τ+δ*(t:ℂ)) * K t)
      volume (-1) 1 := by
    exact sourceAction_upper_gapSidePathIntegrand_intervalIntegrable
      hp hp1 ψ hreal n hopen 0
  have hzero : (∫ t in (-1:ℝ)..1, F (τ+δ*(t:ℂ)) * K t) = 0 := by
    exact sourceCriticalRoot_gapSidePathIntegral_eq_zero
      hp hp1 ψ hreal n hopen true
  change (∫ t in (-1:ℝ)..1,
      ((τ+δ*(t:ℂ))-(q:ℂ)) * F (τ+δ*(t:ℂ)) * K t) =
    ∫ t in (-1:ℝ)..1,
      ((τ+δ*(t:ℂ))-0) * F (τ+δ*(t:ℂ)) * K t
  have hpoint (t : ℝ) :
      ((τ+δ*(t:ℂ))-(q:ℂ)) * F (τ+δ*(t:ℂ)) * K t =
        ((τ+δ*(t:ℂ))-0) * F (τ+δ*(t:ℂ)) * K t -
          (q:ℂ) * (F (τ+δ*(t:ℂ)) * K t) := by
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_sub h0 (hF.const_mul (q:ℂ)),
    intervalIntegral.integral_const_mul,hzero]
  simp

/-- At the indexed critical point, the upper-side cosine integral
contains two copies of the gap half-width. The remaining integrand is
the shifted cosine square times the complementary spectral factor. -/
theorem sourceAction_upper_cosineBoundaryIntegral_critical_model
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let τ := sourceStandardRootMidpoint hp hp1 ψ n
    let δ := sourceStandardRootHalfGap hp hp1 ψ n
    let crit := canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    sourceAction_cosineBoundaryIntegral hp hp1 ψ n (crit.re:ℂ) true =
      -δ^2 *
        ∫ θ in (0:ℝ)..Real.pi,
          ((crit-τ)/δ - (Real.cos θ:ℂ))^2 *
            (I * sourceCriticalRootRatioExtension hp hp1 n ψ
              (τ+δ*(Real.cos θ:ℂ))) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let crit := canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let D (z : ℂ) := deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z
  let F (z : ℂ) := sourceCriticalRootRatioExtension hp hp1 n ψ z
  have hδne : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0 :=
    sourceCanonicalPeriodicGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hcritreal : crit.im = 0 :=
    canonicalCriticalPoints_im_eq_zero hp hp1 _ (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) n
  have hcritEq : (crit.re:ℂ) = crit := by
    apply Complex.ext
    · simp
    · simpa using hcritreal.symm
  have hpoint (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
      let t := Real.cos θ
      let z := τ+δ*(t:ℂ)
      ((z-(crit.re:ℂ)) *
        (D z / sourceCanonicalRootGapUpperValue hp hp1 ψ n t)) *
          (δ*(Real.sin θ:ℂ)) =
        -δ^2 * (((crit-τ)/δ-(t:ℂ))^2 * (I*F z)) := by
    let t := Real.cos θ
    let z := τ+δ*(t:ℂ)
    have ht : t ∈ Set.Ioo (-1) 1 := cos_mem_gapInterior hθ
    have hdom : sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
        sourceStandardRootOmittedDomain hp hp1 ψ n :=
      sourceStandardRootGapSegment_subset_omittedDomain_of_realType
        hp hp1 ψ hreal n ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
    have hfactor :=
      discriminant_derivative_div_canonicalRootGapUpperValue_eq_selectedFactor
        hp hp1 ψ n t hgap ht hdom
    change D z / sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
      (crit-z)*F z / (-δ*I*(Real.sqrt (1-t^2):ℂ)) at hfactor
    have hsqrt : Real.sqrt (1-t^2) = Real.sin θ :=
      (Real.sin_eq_sqrt_one_sub_cos_sq hθ.1.le hθ.2.le).symm
    have hsin : (Real.sin θ:ℂ) ≠ 0 := by
      exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
    have hoffset : crit-z = δ*((crit-τ)/δ-(t:ℂ)) := by
      dsimp [z]
      field_simp [hδne]
      ring
    change ((z-(crit.re:ℂ)) *
      (D z / sourceCanonicalRootGapUpperValue hp hp1 ψ n t)) *
        (δ*(Real.sin θ:ℂ)) =
      -δ^2 * (((crit-τ)/δ-(t:ℂ))^2 * (I*F z))
    rw [hfactor, hcritEq, hsqrt]
    have hden : -δ*I*(Real.sin θ:ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hδne) I_ne_zero) hsin
    have hkernel : (δ*(Real.sin θ:ℂ)) /
        (-δ*I*(Real.sin θ:ℂ)) = I := by
      apply (div_eq_iff hden).2
      calc
        δ*(Real.sin θ:ℂ) = -(I^2)*(δ*(Real.sin θ:ℂ)) := by
          simp [Complex.I_sq]
        _ = I*(-δ*I*(Real.sin θ:ℂ)) := by ring
    calc
      ((z-crit) * ((crit-z)*F z /
          (-δ*I*(Real.sin θ:ℂ)))) * (δ*(Real.sin θ:ℂ)) =
          ((z-crit)*(crit-z)*F z) *
            ((δ*(Real.sin θ:ℂ))/(-δ*I*(Real.sin θ:ℂ))) := by ring
      _ = ((z-crit)*(crit-z)*F z) * I := by rw [hkernel]
      _ = -δ^2 * (((crit-τ)/δ-(t:ℂ))^2 * (I*F z)) := by
        rw [show z-crit = -(crit-z) by ring, hoffset]
        ring
  unfold sourceAction_cosineBoundaryIntegral
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
  intro θ hθ
  exact hpoint θ hθ

/-- On an open real-type gap, four times the actual normalized action
is exactly the shifted cosine model. The regular factor is the deleted
critical-root quotient, with the phase chosen by the canonical root. -/
theorem sourceRawNormalizedAction_eq_cosineModel_of_openRealGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let τ := sourceStandardRootMidpoint hp hp1 ψ n
    let δ := sourceStandardRootHalfGap hp hp1 ψ n
    let crit := canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    4 * sourceRawNormalizedAction hp hp1 n ψ =
      normalizedActionCosineModel ((crit-τ)/δ)
        (fun θ => I * sourceCriticalRootRatioExtension hp hp1 n ψ
          (τ+δ*(Real.cos θ:ℂ))) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let crit := canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let J : ℂ := ∫ θ in (0:ℝ)..Real.pi,
    ((crit-τ)/δ - (Real.cos θ:ℂ))^2 *
      (I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (τ+δ*(Real.cos θ:ℂ)))
  have hδne : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hgapδ : sourcePeriodicGapDisplacement hp hp1 ψ n = 2*δ := by
    simp only [δ,sourceStandardRootHalfGap,sourcePeriodicGapDisplacement_apply]
    ring
  have hAction : sourceComplexAction hp hp1 n ψ =
      (2*(Real.pi:ℂ)⁻¹)*δ^2*J := by
    rw [sourceComplexAction_eq_upper_cosineBoundaryIntegral
      hp hp1 ψ hreal n hopen]
    rw [← sourceAction_upper_cosineBoundaryIntegral_recenter
      hp hp1 ψ hreal n hopen crit.re]
    rw [sourceAction_upper_cosineBoundaryIntegral_critical_model
      hp hp1 ψ hreal n hopen]
    ring
  change 4 * (sourceComplexAction hp hp1 n ψ /
    (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) =
      (2/(Real.pi:ℂ))*J
  rw [hAction,hgapδ]
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- The complementary factor along a real gap's cosine path is
continuous, including at the two spectral endpoints. -/
theorem sourceCriticalRootRatioExtension_cosine_continuous
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    Continuous (fun θ : ℝ =>
      I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ))) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let F := sourceCriticalRootRatioExtension hp hp1 n ψ
  obtain ⟨W₁,_,_,hreal₁,hpoint⟩ :=
    exists_global_source_gapPoint_mem_omittedDomain hp hp1
  obtain ⟨W₂,_,hreal₂,hext⟩ :=
    exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  have hF : ContinuousOn F (standardRootGapSegment τ δ) := by
    intro z hz
    obtain ⟨t,ht,rfl⟩ := hz
    have hdom := hpoint ψ (hreal₁ hreal) n t ht.1 ht.2
    exact ((hext ψ (hreal₂ hreal) n _ hdom).continuousAt).continuousWithinAt
  have hpath : Continuous (fun θ : ℝ => τ+δ*(Real.cos θ:ℂ)) := by
    fun_prop
  have hseg (θ : ℝ) : τ+δ*(Real.cos θ:ℂ) ∈
      standardRootGapSegment τ δ :=
    ⟨Real.cos θ,⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩,rfl⟩
  exact continuous_const.mul (hF.comp_continuous hpath hseg)

/-- The actual normalized action on a noncollapsed real gap splits
exactly into the universal leading moment, the squared normalized
critical offset, and the integral error of the spectral factor. -/
theorem sourceRawNormalizedAction_eq_one_add_cosineError_of_openRealGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let τ := sourceStandardRootMidpoint hp hp1 ψ n
    let δ := sourceStandardRootHalfGap hp hp1 ψ n
    let crit := canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let χ : ℝ → ℂ := fun θ =>
      I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (τ+δ*(Real.cos θ:ℂ))
    4 * sourceRawNormalizedAction hp hp1 n ψ =
      1 + 2*((crit-τ)/δ)^2 +
        (2/(Real.pi:ℂ)) *
          ∫ θ in (0:ℝ)..Real.pi,
            ((crit-τ)/δ - (Real.cos θ:ℂ))^2 * (χ θ - 1) := by
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
  exact normalizedActionCosineModel_eq_one_add_error
    ((crit-τ)/δ) χ hχ

end NLS.ZakharovShabat
