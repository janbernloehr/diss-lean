import NLS.ZakharovShabat.SourceAngularEtaModelTerminalAngle
import NLS.ZakharovShabat.SourceAngularEtaSheetChoicePathPeriod

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]

/-- The prescribed-sheet model integral has the actual terminal angle
modulo pi even on paths INSIDE the canonical spectral cut. Only the
regular prescribed sheet is needed on the interior of the path. -/
theorem sourceAngularEta_prescribed_model_sub_angle_eq_int_pi
    (hp : p≠⊤) (hp1 : 1<p) (m : ℤ) (ψ : CoeffPair p) (w : ℂ) (hw : w≠0)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R⊆sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    {a : ℂ} (haBall : a∈ball c R)
    (ha : a∈({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m}:Set ℂ))
    (hb : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m∈sourceAngularRegularSheetDisc hp ψ c R w)
    (γ : Path a (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t∈Ioo (0:ℝ) 1, γ.extend t∈sourceAngularRegularSheetDisc hp ψ c R w)
    (δ : CoeffPair p → ℂ) (hδ : δ ψ≠0)
    (hδsq : δ ψ^2=(canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2)^2)
    (e : ℂ)
    (hpoint : sourceAngularBranchCosinePoint hp hp1 m δ (e,ψ)=canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
    (hsin : Complex.sin e=sourceAngularBranchDirichletSine hp hp1 m δ ψ)
    (hnorm : sourceAngularRootSheet hp w (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ)=
      sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 m ψ w)) γ) :
    ∃ k : ℤ, (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 m ψ w) z)-e=
      (k:ℂ)*(Real.pi:ℂ) := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let P := sourceStandardRootOmittedProduct hp hp1 m ψ μ
  let M := ∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 m ψ w) z
  have hP : P ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ m
    (hother (ball_subset_closedBall hb.1))
  have hK : 2*Complex.I*P ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hP
  have hroot : sourceAngularEtaSelectedSheetRoot hp hp1 m ψ w μ = -Complex.I*δ ψ*Complex.sin e := by
    have hfull := sourceAngularBranchCosineRoot_eq_dirichlet_anti hp hp1 m δ ψ e hδ
      (hother (ball_subset_closedBall hb.1)) hpoint hsin
    simp only [sourceAngularBranchCosineRoot,hpoint] at hfull
    change 2*δ ψ*P*Complex.sin e = sourceAntiDiscriminantCandidate hp hp1 ψ μ at hfull
    change sourceAngularRootSheet hp w (μ,ψ)/(2*Complex.I*P) = _
    rw [hnorm,← hfull]
    field_simp [hK]
    rw [I_sq]
    ring
  have hterminal : μ-τ-sourceAngularEtaSelectedSheetRoot hp hp1 m ψ w μ =
      δ ψ*Complex.exp (Complex.I*e) := by
    have hcoord := hpoint
    change τ+δ ψ*Complex.cos e = μ at hcoord
    rw [hroot,mul_comm Complex.I e,Complex.exp_mul_I]
    linear_combination -hcoord
  have hstart : (a-τ)^2 = δ ψ^2 := by
    rw [hδsq]
    simp only [mem_insert_iff,mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;>
      dsimp only [τ,sourceStandardRootMidpoint,canonicalPeriodicMidpoint,canonicalPeriodicGap] <;> ring
  have he := sourceAngularEtaModelSheet_exp_endpoint_pathIntegral hp hp1 m ψ w hw c R
    hother hdata haBall ha hb γ hγ hγD hmodel
  change Complex.exp (Complex.I*M)*(a-τ) = μ-τ-sourceAngularEtaSelectedSheetRoot hp hp1 m ψ w μ at he
  rw [hterminal] at he
  have hsq := congrArg (fun z : ℂ => z^2) he
  rw [mul_pow,mul_pow,hstart,mul_comm (δ ψ^2)] at hsq
  have hexp := mul_right_cancel₀ (pow_ne_zero 2 hδ) hsq
  rw [← Complex.exp_nat_mul (Complex.I*M) 2,← Complex.exp_nat_mul (Complex.I*e) 2] at hexp
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨k,?_⟩
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) I_ne_zero)
  linear_combination hk

end NLS.ZakharovShabat
