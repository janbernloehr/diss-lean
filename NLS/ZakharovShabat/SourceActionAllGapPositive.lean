import NLS.ZakharovShabat.SourceDiscriminantDerivativeParity

/-!
# Positive actions on all open real source gaps

The parity signs of the discriminant derivative and upper canonical
root cancel in their quotient. The weighted upper boundary integral
is the negative arcosh area, and the circle orientation changes its
sign to give a positive action.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem signed_two_deriv_div_signed_two_sqrt
    (s u v : ℝ) (hs : s ≠ 0) (hv : v ≠ 0) :
    (((s*(2*u):ℝ):ℂ) / ((s*(2*v):ℝ):ℂ)) = ((u/v:ℝ):ℂ) := by
  have hsC : (s:ℂ) ≠ 0 := by exact_mod_cast hs
  have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv
  push_cast
  field_simp

/-- The upper weighted boundary integral is the strictly negative
real arcosh area at every open real-type gap. -/
theorem sourceAction_upper_cosineBoundaryIntegral_eq_neg_arcosh_all
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let g := realGapHalfDiscriminant hp (periodOnePotential ψ) n
    sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) true =
      ((-(∫ x in a..b, Real.arcosh (g x)):ℝ):ℂ) := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let g := realGapHalfDiscriminant hp (periodOnePotential ψ) n
  let s : ℝ := ∫ x in a..b,
    (x-q) * (deriv g x / Real.sqrt ((g x)^2-1))
  have hs : s = -(∫ x in a..b, Real.arcosh (g x)) :=
    (realGap_weighted_arcosh_integral_eq_and_neg
      hp hp1 ψ hreal n hopen q).1
  have hpoint (x : ℝ) (hx : x ∈ Ioo a b) :
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
        realGapCanonicalRootUpperValue hp hp1 ψ n x =
      ((deriv g x / Real.sqrt ((g x)^2-1):ℝ):ℂ) := by
    have hrad := realGapHalfDiscriminant_radicand_pos_at_affinePoint
      hp hp1 ψ hreal n hopen
      (realGapInverseCoordinate_mem_Ioo hp hp1 ψ n hx)
    rw [realGapAffinePoint_inverse hp hp1 ψ n hopen x] at hrad
    rw [discriminant_derivative_eq_signed_two_realGapHalfDiscriminant_deriv
      hp hp1 ψ hreal n x,
      realGapCanonicalRootUpperValue_eq_signed_two_sqrt
        hp hp1 ψ hreal n hopen hx]
    exact signed_two_deriv_div_signed_two_sqrt _ _ _
      (pow_ne_zero _ (by norm_num))
      (ne_of_gt (Real.sqrt_pos.mpr hrad))
  have hW : sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) true =
      (s:ℂ) := by
    rw [sourceAction_cosineBoundaryIntegral_eq_gapSidePathIntegral
      hp hp1 ψ hreal n hopen q true,
      sourceAction_upper_gapSidePathIntegral_eq_realIntegral
        hp hp1 ψ hreal n hopen q]
    calc
      (∫ x in a..b, ((x-q:ℝ):ℂ) *
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
          realGapCanonicalRootUpperValue hp hp1 ψ n x)) =
          ∫ x in a..b,
            (((x-q) * (deriv g x / Real.sqrt ((g x)^2-1)):ℝ):ℂ) := by
        apply intervalIntegral.integral_congr_uIoo
        rw [uIoo_of_le hopen.le]
        intro x hx
        change ((x-q:ℝ):ℂ) *
          (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
            realGapCanonicalRootUpperValue hp hp1 ψ n x) =
          (((x-q) * (deriv g x / Real.sqrt ((g x)^2-1)):ℝ):ℂ)
        rw [hpoint x hx]
        push_cast
        ring
      _ = (s:ℂ) := by
        simp only [intervalIntegral.integral_ofReal,s]
  rw [hW,hs]

/-- The upper weighted boundary integral has negative real part on
every open real source gap. -/
theorem sourceAction_upper_cosineBoundaryIntegral_re_neg_all
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (sourceAction_cosineBoundaryIntegral hp hp1 ψ n 0 true).re < 0 := by
  obtain ⟨hsEq,hsNeg⟩ := realGap_weighted_arcosh_integral_eq_and_neg
    hp hp1 ψ hreal n hopen 0
  have heq := sourceAction_upper_cosineBoundaryIntegral_eq_neg_arcosh_all
    hp hp1 ψ hreal n hopen 0
  have hWre := congrArg Complex.re (by
    simpa only [Complex.ofReal_zero] using heq)
  simp only [Complex.ofReal_re] at hWre
  rw [hWre, ← hsEq]
  exact hsNeg

/-- Every sufficiently small midpoint action circle around an open
real-type gap has strictly positive real value. -/
theorem exists_sourceActionCircle_re_pos_on_small_realGapCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Ioc 0 ε,
      0 < (sourceActionCircle hp hp1 ψ c (d+η)).re := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  let W := sourceAction_cosineBoundaryIntegral hp hp1 ψ n 0 true
  obtain ⟨ε,hε,heq⟩ := exists_sourceActionCircle_eq_upperBoundaryIntegral
    hp hp1 ψ hreal n hopen
  have hW : W.re < 0 :=
    sourceAction_upper_cosineBoundaryIntegral_re_neg_all
      hp hp1 ψ hreal n hopen
  have hscale : -(2*(Real.pi:ℂ)⁻¹) = ((-2/Real.pi:ℝ):ℂ) := by
    push_cast
    ring
  have hscaleNeg : -2/Real.pi < 0 :=
    div_neg_of_neg_of_pos (by norm_num) Real.pi_pos
  refine ⟨ε,hε,?_⟩
  intro η hη
  rw [heq η hη]
  change 0 < (-(2*(Real.pi:ℂ)⁻¹)*W).re
  rw [hscale]
  have hmul : 0 < (-2/Real.pi)*W.re :=
    mul_pos_of_neg_of_neg hscaleNeg hW
  simpa [Complex.mul_re] using hmul

/-- On every open real-type gap, the small-circle action is a
strictly positive real number. -/
theorem exists_sourceActionCircle_positive_real_on_small_realGapCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Ioc 0 ε,
      0 < (sourceActionCircle hp hp1 ψ c (d+η)).re ∧
        (sourceActionCircle hp hp1 ψ c (d+η)).im = 0 := by
  obtain ⟨ε₁,hε₁,hpos⟩ :=
    exists_sourceActionCircle_re_pos_on_small_realGapCircles
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hreal⟩ :=
    exists_sourceActionCircle_real_ne_zero_on_small_midpointCircles
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro η hη
  have hη₁ : η ∈ Ioc 0 ε₁ :=
    ⟨hη.1,hη.2.trans (min_le_left _ _)⟩
  have hη₂ : η ∈ Ioc 0 ε₂ :=
    ⟨hη.1,hη.2.trans (min_le_right _ _)⟩
  exact ⟨hpos η hη₁,(hreal η hη₂).1⟩

end NLS.ZakharovShabat
