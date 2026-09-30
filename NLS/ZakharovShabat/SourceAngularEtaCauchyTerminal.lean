import NLS.ZakharovShabat.SourceAngularEtaCauchySheetPrimitive
import NLS.ZakharovShabat.SourceAngularEtaAdmissiblePathPeriod

/-!
# Actual eta remainder terminal values from the analytic Cauchy formula

The Cauchy candidate equals every normalized remainder primitive on
the actual terminal sheet. Its value is independent of the annular
chart and enclosing circle. The literal admissible eta integral equals
its continued-root model integral plus this source analytic remainder,
also at periodic terminals where the remainder is zero.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The explicit candidate recovers any normalized remainder primitive
whose terminal root matches the actual Dirichlet anti-discriminant. -/
theorem etaRemainderCauchyCandidate_eq_normalized_terminal
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    {d : ℂ} {S : ℝ} {w : ℂ} {F E : ℂ → ℂ}
    (hE : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 m s ψ d S w F E)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball d S) (hw : w ≠ 0)
    (hb : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
      sourceAngularRegularSheetDisc hp ψ d S w)
    (hroot : sourceAngularRootSheet hp w
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
      sourceAntiDiscriminantCandidate hp hp1 ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)) :
    sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ ψ =
      E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) := by
  have hC := D.eta_cauchy_sheet_primitive_data ψ hψ ρ hrρ hρR w hw
  have heq := hC.eq_on_overlap hE (D.gap_enclosed ψ hψ) hseg
    ⟨⟨D.terminal_enclosed ψ hψ,hb.2⟩,hb⟩
  dsimp only at heq
  rw [hroot] at heq
  exact heq

/-- Changing the annular chart, its anchor, or its enclosing Cauchy
circle leaves the remainder value unchanged at every complex terminal. -/
theorem etaRemainderCauchyCandidate_eq_on_overlap
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W' V' : Set (CoeffPair p)} {c' : ℤ → ℂ} {T' : ℤ → ℝ}
    {r' R' : ℝ} {z₀' : ℂ}
    (D' : SourceAngularJointAnnulusChartData hp hp1 m s W' V' c' T' r' R' z₀')
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (ρ' : ℝ) (hrρ' : r' < ρ') (hρR' : ρ' < R') :
    EqOn (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ)
      (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c' m) r' R' z₀' ρ') (V ∩ V') := by
  intro ψ hψ
  by_cases hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m
  · rw [D.etaRemainderCauchyCandidate_eq_zero_of_endpoint ψ hψ.1 ρ hend,
      D'.etaRemainderCauchyCandidate_eq_zero_of_endpoint ψ hψ.2 ρ' hend]
  · have hw := sourceDirichletAntiDiscriminant_ne_zero_of_mem_omittedDomain hp hp1 ψ m
      (((D.disc_family ψ hψ.1).contour_family.2 m).2.2.1
        (ball_subset_closedBall ((D.disc_family ψ hψ.1).dirichlet_mem_ball m)))
      (fun h => hend (Or.inl h)) (fun h => hend (Or.inr h))
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
    let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
    have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ m hw
    have heq := D.etaRemainderCauchyCandidate_eq_normalized_terminal ψ hψ.1 ρ hrρ hρR
      (D'.eta_cauchy_sheet_primitive_data ψ hψ.2 ρ' hrρ' hρR' w hw)
      (D'.gap_enclosed ψ hψ.2) hw ⟨D'.terminal_enclosed ψ hψ.2,hbase.1⟩ hbase.2
    dsimp only at heq
    rw [hbase.2] at heq
    exact heq

/-- The terminal formula is analytic throughout any chart on which the
actual moving Dirichlet root is analytic, including endpoint terminals. -/
theorem analyticOnNhd_etaRemainderCauchyCandidate
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (hμ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) V) :
    AnalyticOnNhd ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) V :=
  fun ψ hψ => D.analyticAt_etaRemainderCauchyCandidate ρ hrρ hρR ψ hψ (hμ ψ hψ)

/-- The literal eta integral splits into the continued-root model and
the analytic Cauchy remainder. Root normalization is required only at
a regular terminal; either root sign is allowed at a periodic terminal.
The path may traverse several root charts. -/
theorem eta_admissible_pathIntegral_eq_model_add_cauchy_remainder
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (c m) r Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ) :
    sourceAngularPathIntegral m s Q ψ γ =
      (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q) z) +
        sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ ψ := by
  have hother : closedBall (c m) r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    (closedBall_subset_closedBall (D.inner_lt_outer.trans D.outer_lt_assigned).le).trans
      ((D.disc_family ψ hψ).contour_family.2 m).2.2.1
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
  by_cases hw : w = 0
  · have hend := sourceDirichletRoot_mem_periodicEndpoints_of_antiDiscriminant_eq_zero
      hp hp1 ψ m (hother (ball_subset_closedBall (D.terminal_enclosed ψ hψ))) hw
    have hzero := D.etaRemainderCauchyCandidate_eq_zero_of_endpoint ψ hψ ρ
      (by simpa only [SourceAngularDirichletTerminalIsEndpoint,mem_insert_iff,mem_singleton_iff] using hend)
    rw [hzero,add_zero]
    have hC := D.eta_cauchy_sheet_primitive_data ψ hψ ρ hrρ hρR 1 one_ne_zero
    exact hC.admissible_periodic_terminal_pathIntegral_decomposition hother hend Q γ hQ hγ hint hmodel
  · have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ m hw
    have hC := D.eta_cauchy_sheet_primitive_data ψ hψ ρ hrρ hρR w hw
    have heq := hC.admissible_pathIntegral_decomposition hother hw
      ⟨D.terminal_enclosed ψ hψ,hbase.1⟩ Q γ hQ ((hnorm hw).trans hbase.2.symm) hγ hint hmodel
    dsimp only at heq
    rw [hbase.2] at heq
    exact heq

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
