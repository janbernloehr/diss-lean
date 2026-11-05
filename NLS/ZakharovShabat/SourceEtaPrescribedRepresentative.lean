import NLS.ZakharovShabat.SourceEtaPrescribedModelAngle
import NLS.ZakharovShabat.SourceAngularEtaAnalyticPhase
import NLS.ZakharovShabat.SourceAngularEtaCauchySheetPrimitive

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]
namespace SourceAngularEtaAnalyticChartData
variable {hp : p≠⊤} {hp1 : 1<p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}

/-- The analytic eta representative computes EVERY integrable endpoint
path on the regular prescribed sheet modulo pi, including paths INSIDE
the canonical cut. No outside-gap admissibility data is required. -/
theorem prescribed_pathIntegral_sub_representative_eq_int_pi
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ∈U) (w : ℂ) (hw : w≠0)
    (hb : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m∈
      sourceAngularRegularSheetDisc hp ψ (c m) r w)
    (hnorm : sourceAngularRootSheet hp w (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ)=
      sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t∈Ioo (0:ℝ) 1, γ.extend t∈sourceAngularRegularSheetDisc hp ψ (c m) r w)
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s
      (sourceAngularRootSheet hp w) (z,ψ))) γ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 m ψ w)) γ) :
    ∃ k : ℤ, sourceAngularPathIntegral m s (sourceAngularRootSheet hp w) ψ γ-
      sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε ψ=(k:ℂ)*(Real.pi:ℂ) := by
  have hψV := D.angle.source_subset hψ
  have hother : closedBall (c m) r⊆sourceStandardRootOmittedDomain hp hp1 ψ m :=
    (closedBall_subset_closedBall (D.annulus.inner_lt_outer.trans D.annulus.outer_lt_assigned).le).trans
      ((D.annulus.disc_family ψ hψV).contour_family.2 m).2.2.1
  have haBall := D.annulus.gap_enclosed ψ hψV (left_mem_segment ℝ _ _)
  let E : ℂ → ℂ := fun z => sourceAngularRootSheet hp w (z,ψ)/
    (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ z)*
      sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ (z,ψ)
  have hE := D.annulus.eta_cauchy_sheet_primitive_data ψ hψV ρ D.inner_lt_cauchy D.cauchy_lt_outer w hw
  have hdecomp := sourceAngularEta_prescribed_sheet_endpoint_pathIntegral_decomposition
    hp hp1 m s ψ w _ E hE.hasDerivAt_sheet hE.tendsto_left_sheet hb γ hγ hγD hint hmodel
  have hterm : E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)=
      sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ ψ := by
    dsimp only [E,sourceAngularEtaRemainderCauchyCandidate]
    rw [hnorm]
  obtain ⟨k,hk⟩ := sourceAngularEta_prescribed_model_sub_angle_eq_int_pi hp hp1 m ψ w hw (c m) r
    hother (D.endpoint_data ψ hψ) haBall (by simp) hb γ hγ hγD δ (D.angle.halfGap_ne_zero ψ hψ)
    (D.angle.halfGap_sq ψ hψ) (ε ψ) (D.angle.terminal_coordinates ψ hψ).1
    (D.angle.terminal_coordinates ψ hψ).2 hnorm hmodel
  refine ⟨k+1,?_⟩
  rw [hdecomp,hterm,sourceAngularEtaCauchyRepresentative]
  push_cast
  linear_combination hk

/-- The actual global eta phase is also realized by paths through the
INTERIOR cut, with the terminal prescription retained exactly. -/
theorem exp_two_I_prescribed_pathIntegral_eq_phase
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ∈U) (w : ℂ) (hw : w≠0)
    (hb : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m∈
      sourceAngularRegularSheetDisc hp ψ (c m) r w)
    (hnorm : sourceAngularRootSheet hp w (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ)=
      sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t∈Ioo (0:ℝ) 1, γ.extend t∈sourceAngularRegularSheetDisc hp ψ (c m) r w)
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s
      (sourceAngularRootSheet hp w) (z,ψ))) γ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 m ψ w)) γ) :
    Complex.exp (2*I*sourceAngularPathIntegral m s (sourceAngularRootSheet hp w) ψ γ)=
      sourceAngularEtaAnalyticPhase hp hp1 m s ψ := by
  rw [D.phase_eq_exp_representative ψ hψ]
  obtain ⟨k,hk⟩ := D.prescribed_pathIntegral_sub_representative_eq_int_pi ψ hψ w hw hb hnorm γ hγ hγD hint hmodel
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  exact ⟨k,by linear_combination 2*I*hk⟩

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
