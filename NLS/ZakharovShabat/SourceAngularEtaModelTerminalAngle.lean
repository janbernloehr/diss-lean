import NLS.ZakharovShabat.SourceAngularEtaAdmissiblePathModel
import NLS.ZakharovShabat.SourceAngularComplexDirichletAngle

/-!
# Continued eta model integrals and complex terminal angles

The terminal sine and cosine express the continued-root logarithmic
coordinate as the half-gap times an exponential. Squaring removes the
choice of periodic starting endpoint and half-gap sign. Every integrable
admissible model integral therefore agrees with the terminal angle
modulo pi, including at periodic Dirichlet terminals.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Conditional normalization at regular terminals also fixes the root
at a periodic terminal, since both the root and anti-discriminant vanish. -/
theorem sourceAngularAdmissiblePathRoot_dirichlet_terminal_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (ψ : CoeffPair p)
    {c : ℂ} {R : ℝ} {a : ℂ} {Q : ℂ × CoeffPair p → ℂ}
    {γ : Path a (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)}
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ c R Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)) :
    Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
      sourceAntiDiscriminantCandidate hp hp1 ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) := by
  by_cases hw : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) = 0
  · have hs : Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ)^2 =
        sourceAntiDiscriminantCandidate hp hp1 ψ
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)^2 := by
      have h := hQ.square_root 1 (by norm_num)
      simp only [Path.extend_one] at h
      exact h.trans (sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m)
    rw [hw,zero_pow (by norm_num : 2 ≠ 0)] at hs
    rw [hw]
    exact sq_eq_zero_iff.mp hs
  · exact hnorm hw

namespace SourceAngularAdmissiblePathRootData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {Q : ℂ × CoeffPair p → ℂ} {a : ℂ}
  {γ : Path a (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)}

/-- Either periodic starting endpoint and either analytic half-gap
branch give the same terminal model angle modulo pi. -/
theorem model_pathIntegral_sub_angle_eq_int_pi
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ c R Q γ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (haBall : a ∈ ball c R)
    (hμBall : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball c R)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ))
    (δ : CoeffPair p → ℂ) (hδ : δ ψ ≠ 0)
    (hδsq : δ ψ^2 = (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2)^2)
    (e : ℂ)
    (hpoint : sourceAngularBranchCosinePoint hp hp1 m δ (e,ψ) =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
    (hsin : Complex.sin e = sourceAngularBranchDirichletSine hp hp1 m δ ψ)
    (hnorm : Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
      sourceAntiDiscriminantCandidate hp hp1 ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ) :
    ∃ k : ℤ, (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q) z)-e =
      (k : ℂ)*(Real.pi : ℂ) := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let P := sourceStandardRootOmittedProduct hp hp1 m ψ μ
  let M := ∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q) z
  have hP : P ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ m
    (hother (ball_subset_closedBall hμBall))
  have hK : 2*Complex.I*P ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hP
  have hroot : sourceAngularEtaSelectedPathRoot hp hp1 m ψ Q μ = -Complex.I*δ ψ*Complex.sin e := by
    have hfull := sourceAngularBranchCosineRoot_eq_dirichlet_anti hp hp1 m δ ψ e hδ
      (hother (ball_subset_closedBall hμBall)) hpoint hsin
    simp only [sourceAngularBranchCosineRoot,hpoint] at hfull
    change 2*δ ψ*P*Complex.sin e = sourceAntiDiscriminantCandidate hp hp1 ψ μ at hfull
    change Q (μ,ψ)/(2*Complex.I*P) = _
    rw [hnorm,← hfull]
    field_simp [hK]
    rw [I_sq]
    ring
  have hterminal : μ-τ-sourceAngularEtaSelectedPathRoot hp hp1 m ψ Q μ =
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
  have he := hQ.exp_model_pathIntegral hother hdata haBall hμBall ha hγ hmodel
  change Complex.exp (Complex.I*M)*(a-τ) = μ-τ-sourceAngularEtaSelectedPathRoot hp hp1 m ψ Q μ at he
  rw [hterminal] at he
  have hsq := congrArg (fun z : ℂ => z^2) he
  rw [mul_pow,mul_pow,hstart,mul_comm (δ ψ^2)] at hsq
  have hexp := mul_right_cancel₀ (pow_ne_zero 2 hδ) hsq
  rw [← Complex.exp_nat_mul (Complex.I*M) 2,← Complex.exp_nat_mul (Complex.I*e) 2] at hexp
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨k,?_⟩
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) I_ne_zero)
  linear_combination hk

end SourceAngularAdmissiblePathRootData
end NLS.ZakharovShabat
