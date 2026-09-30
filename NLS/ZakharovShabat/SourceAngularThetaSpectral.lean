import NLS.ZakharovShabat.SourceAngularThetaAnalytic

/-! # Literal admissible spectral formulas for the angle coordinate

Adding the actual convergent beta correction to a normalized eta
integral gives the analytic theta representative modulo pi. For real
potentials the literal integral plus correction is real. Both periodic
anchors and periodic terminals are covered, with actual and model
integrability retained explicitly.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}
  (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
  (ψ : CoeffPair p) (hψ : ψ ∈ U) {a : ℂ}
  (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
    canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
  (Q : ℂ × CoeffPair p → ℂ)
  (γ : Path a (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))
  (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ (c n) r Q γ)
  (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) ≠ 0 →
    Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,ψ) =
      sourceAntiDiscriminantCandidate hp hp1 ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))
  (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
  (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ)
  (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q)) γ)

include D hψ ha hQ hnorm hγ hint hmodel

theorem admissible_angle_sub_representative_eq_int_pi :
    ∃ k : ℤ, sourceAngularPathIntegral n s Q ψ γ+sourceAngularBetaCorrection hp hp1 n s ψ-
      sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ = (k:ℂ)*(Real.pi:ℂ) := by
  obtain ⟨k,hk⟩ := D.admissible_pathIntegral_sub_representative_eq_int_pi ψ hψ ha Q γ hQ hnorm hγ hint hmodel
  exact ⟨k,by simpa only [sourceAngularThetaCauchyRepresentative,add_sub_add_right_eq_sub] using hk⟩

theorem exp_two_I_admissible_angle_eq_theta_phase :
    Complex.exp (2*Complex.I*(sourceAngularPathIntegral n s Q ψ γ+
      sourceAngularBetaCorrection hp hp1 n s ψ)) = sourceAngularThetaAnalyticPhase hp hp1 n s ψ := by
  rw [mul_add,Complex.exp_add,D.exp_two_I_admissible_pathIntegral_eq_phase ψ hψ ha Q γ hQ hnorm hγ hint hmodel]
  rfl

theorem admissible_angle_im_eq_zero_of_realType
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hbeta : (sourceAngularBetaCorrection hp hp1 n s ψ).im = 0) :
    (sourceAngularPathIntegral n s Q ψ γ+sourceAngularBetaCorrection hp hp1 n s ψ).im = 0 := by
  obtain ⟨k,hk⟩ := D.admissible_angle_sub_representative_eq_int_pi ψ hψ ha Q γ hQ hnorm hγ hint hmodel
  have hi := congrArg Complex.im hk
  simpa only [Complex.sub_im,D.theta_representative_im_eq_zero_of_realType hs ψ hψ hreal hbeta,
    Complex.mul_im,Complex.intCast_im,Complex.ofReal_im,mul_zero,zero_mul,add_zero,sub_zero] using hi

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
