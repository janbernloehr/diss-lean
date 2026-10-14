import NLS.ZakharovShabat.SourceRealThetaPhase

/-!
# The oriented angle phase agrees with the literal spectral integral

Starting at the left periodic endpoint fixes exp(i theta), including when
the Dirichlet terminal is periodic. The actual and model integrability
conditions are retained, as in the underlying admissible-path theorems.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {B V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}

/-- The original left-anchor formula determines the full phase, not only its square. -/
theorem exp_I_admissible_angle_eq_realPhase
    (E : SourceAngularEtaAnalyticChartData hp hp1 n s B V U c T r R z₀ ρ δ ε)
    (φ : CoeffPair p) (hφ : φ ∈ U)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n φ (c n) r Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n,φ) =
        sourceAntiDiscriminantCandidate hp hp1 φ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,φ))) γ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n φ Q)) γ) :
    Complex.exp (Complex.I*(sourceAngularPathIntegral n s Q φ γ + sourceAngularBetaCorrection hp hp1 n s φ)) =
      sourceAngularThetaRealPhase hp hp1 n s φ := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
  let τ := sourceStandardRootMidpoint hp hp1 φ n
  let g := canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let M := ∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n φ Q) z
  have hφV := E.angle.source_subset hφ
  have hother : closedBall (c n) r ⊆ sourceStandardRootOmittedDomain hp hp1 φ n :=
    (closedBall_subset_closedBall (E.annulus.inner_lt_outer.trans E.annulus.outer_lt_assigned).le).trans
      ((E.annulus.disc_family φ hφV).contour_family.2 n).2.2.1
  have hP := sourceStandardRootOmittedProduct_ne_zero hp hp1 φ μ n
    (hother (ball_subset_closedBall (E.annulus.terminal_enclosed φ hφV)))
  have hterminal := sourceAngularAdmissiblePathRoot_dirichlet_terminal_eq hp hp1 n φ hQ hnorm
  have hroot : sourceAngularEtaSelectedPathRoot hp hp1 n φ Q μ =
      -Complex.I*sourceDirichletEtaSineNumerator hp hp1 n φ := by
    unfold sourceAngularEtaSelectedPathRoot sourceDirichletEtaSineNumerator
    dsimp only [μ]
    rw [hterminal]
    field_simp
    rw [Complex.I_sq]
    ring
  have he := hQ.exp_model_pathIntegral hother (E.endpoint_data φ hφ)
    (E.annulus.gap_enclosed φ hφV (left_mem_segment ℝ _ _))
    (E.annulus.terminal_enclosed φ hφV) (by simp) hγ hmodel
  have hstart : canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n-τ = -g/2 := by
    dsimp only [τ,g,sourceStandardRootMidpoint,canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  change Complex.exp (Complex.I*M)*(_-τ) = μ-τ-sourceAngularEtaSelectedPathRoot hp hp1 n φ Q μ at he
  rw [hstart,hroot] at he
  have hm : Complex.exp (Complex.I*M) = -2*(μ-τ+Complex.I*sourceDirichletEtaSineNumerator hp hp1 n φ)/g := by
    apply (eq_div_iff hg).mpr
    linear_combination -2*he
  have hdecomp := E.annulus.eta_admissible_pathIntegral_eq_model_add_cauchy_remainder
    φ hφV ρ E.inner_lt_cauchy E.cauchy_lt_outer Q γ hQ hnorm hγ hint hmodel
  rw [hdecomp]
  change Complex.exp (Complex.I*(M+_+_)) = _
  simp only [mul_add,Complex.exp_add]
  rw [hm,sourceAngularThetaRealPhase,sourceGapWeightedEtaCoordinate,
    E.annulus.etaRemainder_eq_cauchyCandidate ρ E.inner_lt_cauchy E.cauchy_lt_outer φ hφV]
  simp only [one_mul]
  dsimp only [μ,τ,g,sourceStandardRootMidpoint]
  ring

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
