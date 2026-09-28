import NLS.ZakharovShabat.SourcePsiEquationOpenGapZero
import NLS.ZakharovShabat.SourcePsiVariationCollapsedGapZero

/-!
# A zero of an entire psi numerator at a collapsed periodic gap

At a collapsed gap the standard root is linear. Cauchy's formula
converts a vanishing psi contour equation into a zero of its entire
numerator at the periodic midpoint.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A zero canonical-root contour integral at a collapsed gap forces
an entire numerator to vanish at the gap midpoint. -/
theorem entireNumerator_zero_at_collapsedGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c₀ R)
    (hdom : closedBall c₀ R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere c₀ R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C(c₀,R),
      f z /
        sourceCanonicalRoot hp hp1 ψ z) = 0) :
    f
      (sourceStandardRootMidpoint hp hp1 ψ m) = 0 := by
  let Φ : ℂ → ℂ := f
  let P : ℂ → ℂ := sourceStandardRootOmittedProduct hp hp1 m ψ
  let g : ℂ → ℂ := fun z => Φ z / P z
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  obtain ⟨W,_,_,hrealW,hdata⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  have hψW : ψ ∈ W := hrealW hψ
  have hPanalytic : AnalyticOnNhd ℂ P
      (sourceStandardRootOmittedDomain hp hp1 ψ m) :=
    sourceStandardRootOmittedProduct_analyticOnNhd_spectral
      hp hp1 m W (hdata m).2.1 ψ hψW
  have hg : AnalyticOnNhd ℂ g (closedBall c₀ R) := by
    intro z hz
    exact (hf z (mem_univ _)).div (hPanalytic z (hdom hz))
        (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m (hdom hz))
  have hτsphere : ∀ z ∈ sphere c₀ R, z ≠ τ := by
    intro z hz he
    have hlt := mem_ball.mp hmid
    have heq := mem_sphere.mp hz
    rw [he] at heq
    exact (ne_of_lt hlt) heq
  have hpoint (z : ℂ) (hz : z ∈ sphere c₀ R) :
      g z / (τ-z) =
        (2*I) * (Φ z / sourceCanonicalRoot hp hp1 ψ z) := by
    have hzDom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
      hdom (sphere_subset_closedBall hz)
    have hPz : P z ≠ 0 :=
      sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m hzDom
    have hCz : sourceCanonicalRoot hp hp1 ψ z ≠ 0 :=
      sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z (hcircle hz)
    have hSz : τ-z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hτsphere z hz))
    change Φ z / P z / (τ-z) =
      (2*I) * (Φ z / sourceCanonicalRoot hp hp1 ψ z)
    rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ z,
      sourceStandardRoot_of_zeroGap hp hp1 ψ m z hgap]
    change Φ z / P z / (τ-z) =
      (2*I) * (Φ z / (2*I*(τ-z)*P z))
    field_simp [hPz,hSz,Complex.I_ne_zero]
  have hInt :
      (∮ z in C(c₀,R), g z / (τ-z)) =
      (2*I) * (∮ z in C(c₀,R),
        Φ z / sourceCanonicalRoot hp hp1 ψ z) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    exact hpoint z hz
  have hIntZero : (∮ z in C(c₀,R), g z / (τ-z)) = 0 := by
    rw [hInt]
    change (2*I) *
      (∮ z in C(c₀,R),
        f z /
          sourceCanonicalRoot hp hp1 ψ z) = 0
    rw [hzero,mul_zero]
  have hCauchy :
      (∮ z in C(c₀,R), (z-τ)⁻¹ * g z) =
        2*(Real.pi:ℂ)*I*g τ := by
    simpa only [smul_eq_mul] using
      (hg.differentiableOn.circleIntegral_sub_inv_smul hmid)
  have hIntValue : (∮ z in C(c₀,R), g z / (τ-z)) =
      -(2*(Real.pi:ℂ)*I)*g τ := by
    have heq :
        (∮ z in C(c₀,R), g z / (τ-z)) =
          ∮ z in C(c₀,R), (-1:ℂ)*((z-τ)⁻¹*g z) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hzt : z-τ ≠ 0 := sub_ne_zero.mpr (hτsphere z hz)
      have htz : τ-z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hτsphere z hz))
      field_simp [hzt,htz]
      ring
    rw [heq,circleIntegral.integral_const_mul,hCauchy]
    ring
  have hgzero : g τ = 0 := by
    rw [hIntValue] at hIntZero
    have hc : -(2*(Real.pi:ℂ)*I) ≠ 0 := by
      apply neg_ne_zero.mpr
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero
    exact (mul_eq_zero.mp hIntZero).resolve_left hc
  have hPτ : P τ ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ τ m
      (hdom (ball_subset_closedBall hmid))
  have hΦzero : Φ τ = 0 := by
    have := congrArg (fun z : ℂ => z * P τ) hgzero
    simpa [g,hPτ] using this
  exact hΦzero

/-- A zero of the actual scalar psi equation at a collapsed gap
forces its entire numerator to vanish at the gap midpoint. -/
theorem sourcePsiCandidate_zero_at_collapsedGap_of_equation_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : Coeff p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c₀ R)
    (hdom : closedBall c₀ R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere c₀ R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : sourcePsiEquationCoordinate hp hp1 n m
      a ψ c₀ R = 0) :
    sourcePsiCandidate n
      (sourceStandardRootMidpoint hp hp1 ψ m,a) = 0 := by
  have hnum : AnalyticOnNhd ℂ
      (fun z => sourcePsiCandidate n (z,a)) univ :=
    (differentiable_sourcePsiCandidate hp hp1 n a).differentiableOn
      |>.analyticOnNhd isOpen_univ
  have hnm : (((n-m : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn)
  rw [sourcePsiEquationCoordinate_eq_raw_circleIntegral] at hzero
  have hIntZero := (mul_eq_zero.mp hzero).resolve_left hnm
  change (∮ z in C(c₀,R),
      sourcePsiCandidate n (z,a) /
        sourceCanonicalRoot hp hp1 ψ z) = 0 at hIntZero
  exact entireNumerator_zero_at_collapsedGap hp hp1 ψ hψ m
    (fun z => sourcePsiCandidate n (z,a)) hnum
      hgap c₀ R hR hmid hdom hcircle hIntZero

end NLS.ZakharovShabat
