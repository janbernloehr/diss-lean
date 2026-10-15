import NLS.ComplexAnalysis.TwoEndpointSquareRootIntegrability
import NLS.ZakharovShabat.SourceAngularAdmissiblePathConstruction

/-!
# Actual angular integrability on transverse admissible paths

A smooth admissible path with quantitative separation from both periodic
endpoints has integrable actual and eta-model one-forms at every open
gap. The numerator and omitted root are the original spectral functions;
only the root's continuous continuation along the path is required.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularAdmissiblePathRootData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
  {Q : ℂ × CoeffPair p → ℂ} {b : ℂ}

/-- A continuous numerator divided by the selected root is integrable along a transverse path. -/
theorem transverse_selectedRoot_curveIntegrable
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (hb : b ∈ ball (P.center:ℂ) P.radius)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (k : ℝ) (hk : 0 < k)
    (hsep : ∀ t ∈ Ioo (0:ℝ) 1,
      k*t*(1-t) ≤ ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-γ.extend t‖ ∧
      k*t*(1-t) ≤ ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-γ.extend t‖)
    (f : ℂ → ℂ) (hf : ContinuousOn f (ball (P.center:ℂ) P.radius)) :
    CurveIntegrable (holomorphicOneForm
      (fun z => f z/sourceAngularEtaSelectedPathRoot hp hp1 m ψ Q z)) γ := by
  have hball := hQ.path_mem_ball (P.gap (left_mem_segment ℝ _ _)) hb
  have hother (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      γ.extend t ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    P.closedBall_subset_omittedDomain (ball_subset_closedBall (hball t ht))
  apply curveIntegrable_div_quadratic_root_of_transverse_bound hgap γ hγ f
    (sourceAngularEtaSelectedPathRoot hp hp1 m ψ Q)
    (hf.comp γ.continuous_extend.continuousOn hball) ?_ ?_ k hk hsep
  · apply hQ.continuous_root.continuousOn.div
      (continuousOn_const.mul (hdata.analytic_omitted.continuousOn.comp
        γ.continuous_extend.continuousOn (fun t ht => hother t (Ioo_subset_Icc_self ht))))
    intro t ht
    exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ _ m (hother t (Ioo_subset_Icc_self ht)))
  · intro t ht
    exact sourceAngularEtaSelectedPathRoot_sq hp hp1 m ψ Q _
      (hQ.square_root t (Ioo_subset_Icc_self ht)) (hother t (Ioo_subset_Icc_self ht))

/-- At an open gap, every actual numerator and the eta model are integrable on the constructed paths. -/
theorem transverse_actual_and_model_curveIntegrable
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (hb : b ∈ ball (P.center:ℂ) P.radius)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (k : ℝ) (hk : 0 < k)
    (hsep : ∀ t ∈ Ioo (0:ℝ) 1,
      k*t*(1-t) ≤ ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-γ.extend t‖ ∧
      k*t*(1-t) ≤ ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-γ.extend t‖)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) :
    (∀ n : ℤ, CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ) ∧
      CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ := by
  constructor
  · intro n
    have hF : ContinuousOn (sourceAngularGapNumerator hp hp1 n m s ψ) (ball (P.center:ℂ) P.radius) :=
      (sourceAngularGapNumerator_analyticOnNhd hp hp1 n m s ψ hdata.analytic_omitted).continuousOn.mono
        (ball_subset_closedBall.trans P.closedBall_subset_omittedDomain)
    have hint := hQ.transverse_selectedRoot_curveIntegrable P γ hdata hb hgap hγ k hk hsep _ hF
    apply (curveIntegrable_holomorphicOneForm_congr_interior _ _ γ ?_).mpr hint
    intro t ht
    have hPne := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ _ m
      (P.closedBall_subset_omittedDomain (ball_subset_closedBall (hQ.interior t ht).1))
    unfold sourceAngularIntegrand sourceAngularGapNumerator sourceAngularEtaSelectedPathRoot
    exact (div_div_div_cancel_right₀ (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hPne) _ _).symm
  · have hint := hQ.transverse_selectedRoot_curveIntegrable P γ hdata hb hgap hγ k hk hsep
      (fun _ => Complex.I) continuousOn_const
    apply (curveIntegrable_holomorphicOneForm_congr_interior _ _ γ ?_).mpr hint
    intro t ht
    unfold sourceAngularEtaPathModelIntegrand sourceAngularEtaSelectedPathRoot
    rw [div_div_eq_mul_div]
    congr 1
    symm
    calc
      _ = 2*(Complex.I^2)*sourceStandardRootOmittedProduct hp hp1 m ψ (γ.extend t) := by ring
      _ = _ := by rw [I_sq]; ring

end SourceAngularAdmissiblePathRootData
end NLS.ZakharovShabat
