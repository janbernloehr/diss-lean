import NLS.ComplexAnalysis.QuadraticFactorVariationContour
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative
import NLS.ZakharovShabat.SourceCanonicalRootGapIsolation
import NLS.ZakharovShabat.SourceDeletedPairOmittedSquare

/-! # The actual canonical midpoint derivative as a discriminant contour

One common open neighborhood of all real sources supports the formula.
The selected disc encloses its two indexed endpoints and avoids all other
periodic cuts. The endpoints may coincide. Every source derivative in the
formula is the derivative of an already constructed spectral coordinate.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- G.7's midpoint contour identity for the actual indexed source coordinate.
Only geometric isolation is required; no gradient or contour identity is assumed. -/
theorem exists_global_source_midpoint_gradient_contour
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ ∈ W, ∀ (n : ℤ) (c : ℂ) (r : ℝ), 0 < r →
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∈ ball c r →
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∈ ball c r →
      closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 φ n → ∀ h : CoeffPair p,
      (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ) h =
      -(2*Real.pi*I : ℂ)⁻¹ * (∮ z in C(c,r),
        canonicalDiscriminant hp (periodOnePotential φ) z*
          ((fderiv ℂ (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h)/
          ((canonicalDiscriminant hp (periodOnePotential φ) z)^2-4)) := by
  obtain ⟨U,hU,_,hUreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨V,hV,_,hVreal,hprod⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  refine ⟨U ∩ V,hU.inter hV,(fun φ hφ => ⟨hUreal hφ,hVreal hφ⟩),?_⟩
  intro φ hφ n c r hr ha hb hisolate h
  let M : CoeffPair p → ℂ := fun ψ => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let G : CoeffPair p → ℂ := fun ψ => (canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2
  have hM : DifferentiableAt ℂ M φ := (hMG φ hφ.1 n).1.differentiableAt
  have hG : DifferentiableAt ℂ G φ := (hMG φ hφ.1 n).2.differentiableAt
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let O := sourceStandardRootOmittedJointDomain hp hp1 V n
  let P : ℂ × CoeffPair p → ℂ := fun t => (sourceStandardRootOmittedJointProduct hp hp1 n t)^2
  have hO : IsOpen O := (hprod n).1
  have hP : AnalyticOnNhd ℂ P O := (hprod n).2.1.pow 2
  have hpoint (z : ℂ) (hz : z ∈ closedBall c r) : (z,φ) ∈ O := ⟨hφ.2,hisolate hz⟩
  let A : ℂ → ℂ := fun z => (fderiv ℂ P (z,φ)) (0,h)
  have hPspectral : AnalyticOnNhd ℂ (fun z => P (z,φ)) (closedBall c r) := by
    intro z hz
    exact (hP (z,φ) (hpoint z hz)).comp
      (f := fun z : ℂ => (z,φ)) (analyticAt_id.prod analyticAt_const)
  have hA : AnalyticOnNhd ℂ A (closedBall c r) := by
    let ev : ((ℂ × CoeffPair p) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,h)
    have hAjoint := ev.comp_analyticOnNhd hP.fderiv
    intro z hz
    exact (hAjoint (z,φ) (hpoint z hz)).comp
      (f := fun z : ℂ => (z,φ)) (analyticAt_id.prod analyticAt_const)
  have hPne (z : ℂ) (hz : z ∈ closedBall c r) : P (z,φ) ≠ 0 :=
    pow_ne_zero 2 ((hprod n).2.2.2 (z,φ) (hpoint z hz))
  apply midpoint_variation_eq_discriminant_contour
    (fun z => canonicalDiscriminant hp (periodOnePotential φ) z)
    (fun z => (fderiv ℂ (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h)
    (fun z => P (z,φ)) A c a b ((fderiv ℂ M φ) h) ((fderiv ℂ G φ) h) r hr ha hb
    hPspectral hA hPne
  · intro z hz
    rw [show P (z,φ) = canonicalDeletedPeriodicProduct hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) n z from
      sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 φ n z
        (hisolate (sphere_subset_closedBall hz))]
    exact canonicalDiscriminant_sq_sub_four_eq_midpoint_mul hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) n z
  · intro z hz
    have hzO := hpoint z (sphere_subset_closedBall hz)
    let Δ : CoeffPair p → ℂ := fun ψ => canonicalDiscriminant hp (periodOnePotential ψ) z
    have hΔ : DifferentiableAt ℂ Δ φ :=
      ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,φ) (mem_univ _)).comp
        (f := fun ψ : CoeffPair p => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
    have hPs : DifferentiableAt ℂ (fun ψ : CoeffPair p => P (z,ψ)) φ :=
      ((hP (z,φ) hzO).comp (f := fun ψ : CoeffPair p => (z,ψ))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
    have hPder : (fderiv ℂ (fun ψ : CoeffPair p => P (z,ψ)) φ) h = A z := by
      rw [fderiv_source_section_eq_joint P z φ (hP (z,φ) hzO).differentiableAt]
      simp [A]
    have hnear : (fun ψ : CoeffPair p => (Δ ψ)^2-4) =ᶠ[𝓝 φ]
        (fun ψ : CoeffPair p => -4*((z-M ψ)^2-G ψ/4)*P (z,ψ)) := by
      have hopen : IsOpen {ψ : CoeffPair p | (z,ψ) ∈ O} :=
        hO.preimage (continuous_const.prodMk continuous_id)
      filter_upwards [hopen.mem_nhds hzO] with ψ hψ
      rw [show P (z,ψ) = canonicalDeletedPeriodicProduct hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n z from
        sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ n z hψ.2]
      exact canonicalDiscriminant_sq_sub_four_eq_midpoint_mul hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n z
    have hleft := ((hΔ.hasFDerivAt.pow 2).sub_const (4 : ℂ)).fderiv
    have hright := ((((hasFDerivAt_const z φ).sub hM.hasFDerivAt).pow 2).sub
      (hG.hasFDerivAt.mul_const (4 : ℂ)⁻¹)).const_mul (-4)
    have hright' := (hright.fun_mul hPs.hasFDerivAt).fderiv
    simp only [Pi.sub_apply] at hright'
    simp only [div_eq_mul_inv] at hnear
    have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hnear.fderiv_eq
    rw [hleft,hright'] at he
    simp only [add_apply,sub_apply,smul_apply,smul_eq_mul,zero_apply,two_smul] at he
    rw [hPder,show M φ = (a+b)/2 from rfl,show G φ = (b-a)^2 from rfl] at he
    change 2*Δ φ*((fderiv ℂ Δ φ) h) = _
    linear_combination he

/-- The actual midpoint contour formula at every real source, including closed gaps. -/
theorem real_source_midpoint_gradient_contour
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (hφ : φ ∈ realTypeSourceLocus p)
    (n : ℤ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∈ ball c r)
    (hb : canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∈ ball c r)
    (hisolate : closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 φ n) (h : CoeffPair p) :
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ) h =
    -(2*Real.pi*I : ℂ)⁻¹ * (∮ z in C(c,r),
      canonicalDiscriminant hp (periodOnePotential φ) z*
        ((fderiv ℂ (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h)/
        ((canonicalDiscriminant hp (periodOnePotential φ) z)^2-4)) := by
  obtain ⟨W,_,hWreal,hW⟩ := exists_global_source_midpoint_gradient_contour hp hp1
  exact hW φ (hWreal hφ) n c r hr ha hb hisolate h

end NLS.ZakharovShabat
