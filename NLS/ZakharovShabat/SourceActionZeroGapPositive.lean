import NLS.ZakharovShabat.SourceCanonicalRootZeroUpperSign
import NLS.ZakharovShabat.SourceActionMidpointCircleValue

/-!
# Positivity of the action on an open central real gap

The upper canonical-root boundary value on the central gap is the
positive arcosh denominator. The discriminant derivative has the
matching even-parity sign, so the weighted upper boundary integral
equals the strictly negative real arcosh integral. The clockwise
stadium-to-circle orientation then makes the action positive.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At even index zero, the complex discriminant derivative is twice
the derivative of the real half-discriminant. -/
theorem discriminant_derivative_eq_two_realGapHalfDiscriminant_deriv_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (x : ℝ) :
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) =
      ((2*deriv (realGapHalfDiscriminant hp
        (periodOnePotential ψ) 0) x:ℝ):ℂ) := by
  let φ := periodOnePotential ψ
  let D : ℝ → ℝ := fun y => (canonicalDiscriminant hp φ (y:ℂ)).re
  have hdiff : Differentiable ℂ (canonicalDiscriminant hp φ) :=
    fun z => (analyticOnNhd_canonicalDiscriminant hp hp1 φ
      (periodOnePotential_mem ψ) z (mem_univ _)).differentiableAt
  have hDderiv : deriv D x =
      (deriv (canonicalDiscriminant hp φ) (x:ℂ)).re :=
    NLS.ComplexAnalysis.deriv_real_axis_re _ hdiff x
  have him := discriminant_derivative_im_eq_zero_of_realType
    hp hp1 φ (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) x
  have hcast : ((deriv (canonicalDiscriminant hp φ) (x:ℂ)).re:ℂ) =
      deriv (canonicalDiscriminant hp φ) (x:ℂ) := by
    apply Complex.ext
    · rfl
    · exact him.symm
  have hg : realGapHalfDiscriminant hp φ 0 = fun y : ℝ => D y/2 := by
    funext y
    simp [realGapHalfDiscriminant,D]
  have hgderiv : deriv (realGapHalfDiscriminant hp φ 0) x =
      deriv D x/2 := by rw [hg,deriv_div_const]
  rw [← hcast]
  congr 1
  rw [hgderiv,hDderiv]
  ring

private theorem two_deriv_div_two_sqrt_zero (u v : ℝ) (hv : v ≠ 0) :
    (((2*u:ℝ):ℂ) / ((2*v:ℝ):ℂ)) = ((u/v:ℝ):ℂ) := by
  have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv
  push_cast
  field_simp

/-- The central weighted upper boundary integral is the negative
real arcosh area. -/
theorem sourceAction_upper_cosineBoundaryIntegral_eq_neg_arcosh_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re)
    (q : ℝ) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0).re
    let g := realGapHalfDiscriminant hp (periodOnePotential ψ) 0
    sourceAction_cosineBoundaryIntegral hp hp1 ψ 0 (q:ℂ) true =
      ((-(∫ x in a..b, Real.arcosh (g x)):ℝ):ℂ) := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) 0).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) 0).re
  let g := realGapHalfDiscriminant hp (periodOnePotential ψ) 0
  let s : ℝ := ∫ x in a..b,
    (x-q) * (deriv g x / Real.sqrt ((g x)^2-1))
  have hs : s = -(∫ x in a..b, Real.arcosh (g x)) :=
    (realGap_weighted_arcosh_integral_eq_and_neg
      hp hp1 ψ hreal 0 hopen q).1
  have hpoint (x : ℝ) (hx : x ∈ Ioo a b) :
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
        realGapCanonicalRootUpperValue hp hp1 ψ 0 x =
      ((deriv g x / Real.sqrt ((g x)^2-1):ℝ):ℂ) := by
    have hrad := realGapHalfDiscriminant_radicand_pos_at_affinePoint
      hp hp1 ψ hreal 0 hopen
      (realGapInverseCoordinate_mem_Ioo hp hp1 ψ 0 hx)
    rw [realGapAffinePoint_inverse hp hp1 ψ 0 hopen x] at hrad
    rw [discriminant_derivative_eq_two_realGapHalfDiscriminant_deriv_zero
      hp hp1 ψ hreal x,
      realGapCanonicalRootUpperValue_eq_two_sqrt_zero
        hp hp1 ψ hreal hopen hx]
    exact two_deriv_div_two_sqrt_zero _ _
      (ne_of_gt (Real.sqrt_pos.mpr hrad))
  have hW : sourceAction_cosineBoundaryIntegral hp hp1 ψ 0 (q:ℂ) true =
      (s:ℂ) := by
    rw [sourceAction_cosineBoundaryIntegral_eq_gapSidePathIntegral
      hp hp1 ψ hreal 0 hopen q true,
      sourceAction_upper_gapSidePathIntegral_eq_realIntegral
        hp hp1 ψ hreal 0 hopen q]
    calc
      (∫ x in a..b, ((x-q:ℝ):ℂ) *
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
          realGapCanonicalRootUpperValue hp hp1 ψ 0 x)) =
          ∫ x in a..b,
            (((x-q) * (deriv g x / Real.sqrt ((g x)^2-1)):ℝ):ℂ) := by
        apply intervalIntegral.integral_congr_uIoo
        rw [uIoo_of_le hopen.le]
        intro x hx
        change ((x-q:ℝ):ℂ) *
          (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
            realGapCanonicalRootUpperValue hp hp1 ψ 0 x) =
          (((x-q) * (deriv g x / Real.sqrt ((g x)^2-1)):ℝ):ℂ)
        rw [hpoint x hx]
        push_cast
        ring
      _ = (s:ℂ) := by
        simp only [intervalIntegral.integral_ofReal,s]
  rw [hW,hs]

/-- The upper weighted boundary integral has strictly negative real
value on an open central real-type gap. -/
theorem sourceAction_upper_cosineBoundaryIntegral_re_neg_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re) :
    (sourceAction_cosineBoundaryIntegral hp hp1 ψ 0 0 true).re < 0 := by
  obtain ⟨hsEq,hsNeg⟩ := realGap_weighted_arcosh_integral_eq_and_neg
    hp hp1 ψ hreal 0 hopen 0
  have heq := sourceAction_upper_cosineBoundaryIntegral_eq_neg_arcosh_zero
    hp hp1 ψ hreal hopen 0
  have hWre := congrArg Complex.re (by
    simpa only [Complex.ofReal_zero] using heq)
  simp only [Complex.ofReal_re] at hWre
  rw [hWre, ← hsEq]
  exact hsNeg

/-- Every sufficiently small midpoint action circle around an open
central real-type gap has strictly positive real value. -/
theorem exists_sourceActionCircle_re_pos_on_small_zeroGapCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Ioc 0 ε,
      0 < (sourceActionCircle hp hp1 ψ c (d+η)).re := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) 0
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) 0
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  let W := sourceAction_cosineBoundaryIntegral hp hp1 ψ 0 0 true
  obtain ⟨ε,hε,heq⟩ := exists_sourceActionCircle_eq_upperBoundaryIntegral
    hp hp1 ψ hreal 0 hopen
  have hW : W.re < 0 :=
    sourceAction_upper_cosineBoundaryIntegral_re_neg_zero
      hp hp1 ψ hreal hopen
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

/-- The central open-gap action is a strictly positive real number
on every sufficiently small midpoint circle. -/
theorem exists_sourceActionCircle_positive_real_on_small_zeroGapCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) 0
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Ioc 0 ε,
      0 < (sourceActionCircle hp hp1 ψ c (d+η)).re ∧
        (sourceActionCircle hp hp1 ψ c (d+η)).im = 0 := by
  obtain ⟨ε₁,hε₁,hpos⟩ :=
    exists_sourceActionCircle_re_pos_on_small_zeroGapCircles
      hp hp1 ψ hreal hopen
  obtain ⟨ε₂,hε₂,hreal⟩ :=
    exists_sourceActionCircle_real_ne_zero_on_small_midpointCircles
      hp hp1 ψ hreal 0 hopen
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro η hη
  have hη₁ : η ∈ Ioc 0 ε₁ :=
    ⟨hη.1,hη.2.trans (min_le_left _ _)⟩
  have hη₂ : η ∈ Ioc 0 ε₂ :=
    ⟨hη.1,hη.2.trans (min_le_right _ _)⟩
  exact ⟨hpos η hη₁,(hreal η hη₂).1⟩

end NLS.ZakharovShabat
