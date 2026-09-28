import NLS.ZakharovShabat.SourcePsiSelectedJacobianKernelContour
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic
import NLS.ZakharovShabat.SourceCanonicalRootProduct
import NLS.ZakharovShabat.SourcePsiNearFreeCollapsedGap

/-!
# A zero of the psi variation at a collapsed gap

At a collapsed periodic gap, the standard root is linear. Cauchy's
formula converts the zero variation contour integral into vanishing
of the entire numerator variation at the gap midpoint. This part of
the gap-zero argument does not require a real root direction.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Vanishing of the variation contour integral at a collapsed gap
forces the entire numerator variation to vanish at its midpoint. -/
theorem sourcePsiCandidateVariation_zero_at_collapsedGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (a h : Coeff p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c₀ R)
    (hdom : closedBall c₀ R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere c₀ R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C(c₀,R),
      sourcePsiCandidateVariation n a h z /
        sourceCanonicalRoot hp hp1 ψ z) = 0) :
    sourcePsiCandidateVariation n a h
      (sourceStandardRootMidpoint hp hp1 ψ m) = 0 := by
  let Φ : ℂ → ℂ := sourcePsiCandidateVariation n a h
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
    exact ((analyticOnNhd_sourcePsiCandidateVariation hp hp1 n a h)
      z (mem_univ _)).div (hPanalytic z (hdom hz))
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
        sourcePsiCandidateVariation n a h z /
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

/-- A selected Jacobian kernel direction, including a complex one,
gives a zero of the entire variation at each collapsed gap midpoint. -/
theorem sourcePsiSelectedJacobian_kernel_variation_zero_at_collapsedGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (hmn : m ≠ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (hR : 0 < R m)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball (c m) (R m))
    (hdom : closedBall (c m) (R m) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (c m) (R m) ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (h : DeletedCoeff p n)
    (hkernel : sourcePsiSelectedRootJacobian hp hp1 n c R a ψ h = 0) :
    sourcePsiCandidateVariation n (a : Coeff p) (h : Coeff p)
      (sourceStandardRootMidpoint hp hp1 ψ m) = 0 := by
  have hzero := sourcePsiSelectedRootJacobian_kernel_variation_contour_zero
    hp hp1 n c R U hUopen hcoord hdiff a ψ hpair hψ
      m hmn hR.le hcircle h hkernel
  exact sourcePsiCandidateVariation_zero_at_collapsedGap
    hp hp1 ψ hψ n m (a : Coeff p) (h : Coeff p)
      hgap (c m) (R m) hR hmid hdom hcircle hzero

end NLS.ZakharovShabat
