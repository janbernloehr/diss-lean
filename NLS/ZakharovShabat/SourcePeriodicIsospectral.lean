import NLS.ComplexAnalysis.QuadraticFactorStationarity
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative
import NLS.ZakharovShabat.SourceIsospectralDirection
import NLS.ZakharovShabat.SourceCanonicalRootGapIsolation
import NLS.ZakharovShabat.SourceDeletedPairOmittedSquare

/-! # Actual periodic symmetric data are stationary in isospectral directions

Differentiate the actual discriminant quadratic factorization. The
omitted standard-root product supplies an analytic nonzero remainder
through the selected gap. A double root is handled by the spectral
derivative of the linearized identity, without dividing by the gap.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both actual symmetric periodic coordinates have zero source
variation in any isospectral direction, including a collapsed gap. -/
theorem fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (h : CoeffPair p)
    (hiso : SourceIsospectralDirection hp φ h) (n : ℤ) :
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ) h = 0 ∧
    (fderiv ℂ (fun ψ : CoeffPair p => (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) φ) h = 0 := by
  let M : CoeffPair p → ℂ := fun ψ => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let G : CoeffPair p → ℂ := fun ψ => (canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2
  obtain ⟨W,_,_,hWreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hM : DifferentiableAt ℂ M φ := (hMG φ (hWreal hreal) n).1.differentiableAt
  have hG : DifferentiableAt ℂ G φ := (hMG φ (hWreal hreal) n).2.differentiableAt
  obtain ⟨V,_,_,hVreal,hprod⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  let O := sourceStandardRootOmittedJointDomain hp hp1 V n
  let P : ℂ × CoeffPair p → ℂ := fun t => (sourceStandardRootOmittedJointProduct hp hp1 n t)^2
  have hO : IsOpen O := (hprod n).1
  have hP : AnalyticOnNhd ℂ P O := (hprod n).2.1.pow 2
  let D : Set ℂ := {z | (z,φ) ∈ O}
  have hD : IsOpen D := hO.preimage (continuous_id.prodMk continuous_const)
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  obtain ⟨U,_,_,hUreal,hdisjoint⟩ := exists_global_source_disjoint_periodicSegments hp hp1
  have hgap : sourcePeriodicSegment hp hp1 φ n ⊆ D := by
    intro z hz
    refine ⟨hVreal hreal,?_⟩
    intro m hmn
    exact Set.disjoint_left.mp (hdisjoint φ (hUreal hreal) n m (Ne.symm hmn)) hz
  have ha : a ∈ D := hgap (left_mem_segment ℝ a b)
  have hb : b ∈ D := hgap (right_mem_segment ℝ a b)
  let A : ℂ → ℂ := fun z => (fderiv ℂ P (z,φ)) (0,h)
  have hPz : DifferentiableAt ℂ (fun z : ℂ => P (z,φ)) a :=
    ((hP (a,φ) ha).comp (f := fun z : ℂ => (z,φ))
      (analyticAt_id.prod analyticAt_const)).differentiableAt
  have hAz : DifferentiableAt ℂ A a := by
    have hd := (hP.fderiv (a,φ) ha).differentiableAt
    have he := hd.hasFDerivAt.clm_apply (hasFDerivAt_const ((0,h) : ℂ × CoeffPair p) (a,φ))
    have hi : HasDerivAt (fun z : ℂ => (z,φ)) (1,0) a := by
      simpa using (hasDerivAt_id a).prodMk (hasDerivAt_const a φ)
    exact (he.comp_hasDerivAt a hi).differentiableAt
  have hPa : P (a,φ) ≠ 0 := pow_ne_zero 2 ((hprod n).2.2.2 (a,φ) ha)
  have hPb : P (b,φ) ≠ 0 := pow_ne_zero 2 ((hprod n).2.2.2 (b,φ) hb)
  have hzero (z : ℂ) (hz : z ∈ D) :
      (-2*(z-(a+b)/2)*((fderiv ℂ M φ) h)-((fderiv ℂ G φ) h)/4)*P (z,φ)+
        ((z-(a+b)/2)^2-(b-a)^2/4)*A z = 0 := by
    let Δ : CoeffPair p → ℂ := fun ψ => canonicalDiscriminant hp (periodOnePotential ψ) z
    have hΔ : DifferentiableAt ℂ Δ φ :=
      ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,φ) (mem_univ _)).comp
        (f := fun ψ : CoeffPair p => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
    have hPs : DifferentiableAt ℂ (fun ψ : CoeffPair p => P (z,ψ)) φ :=
      ((hP (z,φ) hz).comp (f := fun ψ : CoeffPair p => (z,ψ))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
    have hPder : (fderiv ℂ (fun ψ : CoeffPair p => P (z,ψ)) φ) h = A z := by
      rw [fderiv_source_section_eq_joint P z φ (hP (z,φ) hz).differentiableAt]
      simp [A]
    have hnear : (fun ψ : CoeffPair p => (Δ ψ)^2-4) =ᶠ[𝓝 φ]
        (fun ψ : CoeffPair p => -4*((z-M ψ)^2-G ψ/4)*P (z,ψ)) := by
      have hsourceOpen : IsOpen {ψ : CoeffPair p | (z,ψ) ∈ O} :=
        hO.preimage (continuous_const.prodMk continuous_id)
      filter_upwards [hsourceOpen.mem_nhds hz] with ψ hψ
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
    have hΔzero : (fderiv ℂ Δ φ) h = 0 := hiso z
    rw [hΔzero,hPder] at he
    rw [show M φ = (a+b)/2 from rfl,show G φ = (b-a)^2 from rfl] at he
    linear_combination he/4
  exact quadratic_factor_variations_eq_zero a b ((fderiv ℂ M φ) h) ((fderiv ℂ G φ) h)
    (fun z => P (z,φ)) A D hD ha hb hPa hPb hPz hAz hzero

/-- Every actual action Hamiltonian fixes both symmetric coordinates
at every periodic index, including all central and collapsed gaps. -/
theorem fderiv_canonicalPeriodicMidpoint_squaredGap_sourceHamiltonianVector_action_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ)
      (sourceHamiltonianVector h2p (sourceComplexAction hp hp1 m) φ) = 0 ∧
    (fderiv ℂ (fun ψ : CoeffPair p => (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) φ)
      (sourceHamiltonianVector h2p (sourceComplexAction hp hp1 m) φ) = 0 :=
  fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero hp hp1 φ hreal _
    (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ hreal m) n

/-- The actual periodic midpoint and squared gap commute with every
actual indexed action. No nonzero-gap premise is needed. -/
theorem sourceBracket_canonicalPeriodicMidpoint_squaredGap_action_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (sourceComplexAction hp hp1 m) φ = 0 ∧
    sourceBracket h2p (fun ψ : CoeffPair p => (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2)
      (sourceComplexAction hp hp1 m) φ = 0 := by
  simpa only [fderiv_apply_sourceHamiltonianVector] using
    fderiv_canonicalPeriodicMidpoint_squaredGap_sourceHamiltonianVector_action_eq_zero
      hp hp1 h2p φ hreal n m

end NLS.ZakharovShabat
