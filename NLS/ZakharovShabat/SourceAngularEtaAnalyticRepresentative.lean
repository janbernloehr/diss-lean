import NLS.ZakharovShabat.SourceAngularEtaModelTerminalAngle
import NLS.ZakharovShabat.SourceAngularEtaPeriodicAnchor
import NLS.ZakharovShabat.SourceAngularComplexAngleCommonDomain

/-!
# Full analytic eta representatives from complex angles and remainders

The terminal angle minus pi plus the analytic Cauchy remainder is an
actual local eta representative. It agrees modulo pi with every
integrable admissible spectral integral normalized at the Dirichlet
terminal, with either periodic starting endpoint. Different half-gap
branches, annular charts, and terminal angle choices give representatives
that agree modulo pi on their common source domain.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularEtaCauchyRepresentative
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (c : ℂ) (r R : ℝ) (z₀ : ℂ) (ρ : ℝ) (ε : CoeffPair p → ℂ) (ψ : CoeffPair p) : ℂ :=
  ε ψ-(Real.pi : ℂ)+sourceAngularEtaRemainderCauchyCandidate hp hp1 m s c r R z₀ ρ ψ

/-- A full analytic eta chart, with constructed annular and angle data
and the actual spectral regularity needed for continued-root integrals. -/
structure SourceAngularEtaAnalyticChartData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (W V U : Set (CoeffPair p)) (c : ℤ → ℂ) (T : ℤ → ℝ)
    (r R : ℝ) (z₀ : ℂ) (ρ : ℝ) (δ ε : CoeffPair p → ℂ) : Prop where
  annulus : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀
  inner_lt_cauchy : r < ρ
  cauchy_lt_outer : ρ < R
  angle : SourceAngularComplexDirichletAngleData hp hp1 m V U δ ε
  endpoint_data : ∀ ψ ∈ U, SourceAngularEndpointSpectralData hp hp1 ψ m
  eta_analytic : AnalyticOnNhd ℂ (sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε) U

namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}

theorem gap_ne_zero
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0 := by
  intro hzero
  have hs := D.angle.halfGap_sq ψ hψ
  rw [hzero,zero_div,zero_pow (by norm_num : 2 ≠ 0)] at hs
  exact D.angle.halfGap_ne_zero ψ hψ (sq_eq_zero_iff.mp hs)

/-- All admissible continued roots with the actual terminal
normalization have this analytic eta value modulo pi. The anchor may
be either periodic endpoint and the terminal may itself be periodic. -/
theorem admissible_pathIntegral_sub_representative_eq_int_pi
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) {a : ℂ}
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ))
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path a (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (c m) r Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ) :
    ∃ k : ℤ, sourceAngularPathIntegral m s Q ψ γ-
      sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε ψ = (k : ℂ)*(Real.pi : ℂ) := by
  have hψV := D.angle.source_subset hψ
  have hother : closedBall (c m) r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    (closedBall_subset_closedBall (D.annulus.inner_lt_outer.trans D.annulus.outer_lt_assigned).le).trans
      ((D.annulus.disc_family ψ hψV).contour_family.2 m).2.2.1
  have haBall : a ∈ ball (c m) r := by
    simp only [mem_insert_iff,mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact D.annulus.gap_enclosed ψ hψV (left_mem_segment ℝ _ _)
    · exact D.annulus.gap_enclosed ψ hψV (right_mem_segment ℝ _ _)
  have heq := D.annulus.eta_periodic_anchor_pathIntegral_eq_model_add_cauchy_remainder
    ψ hψV ρ D.inner_lt_cauchy D.cauchy_lt_outer ha Q γ hQ hnorm hγ hint hmodel
  obtain ⟨k,hk⟩ := hQ.model_pathIntegral_sub_angle_eq_int_pi hother (D.endpoint_data ψ hψ)
    haBall (D.annulus.terminal_enclosed ψ hψV) ha δ
    (D.angle.halfGap_ne_zero ψ hψ) (D.angle.halfGap_sq ψ hψ) (ε ψ)
    (D.angle.terminal_coordinates ψ hψ).1 (D.angle.terminal_coordinates ψ hψ).2
    (sourceAngularAdmissiblePathRoot_dirichlet_terminal_eq hp hp1 m ψ hQ hnorm) hγ hmodel
  refine ⟨k+1,?_⟩
  rw [heq]
  simp only [sourceAngularEtaCauchyRepresentative,Int.cast_add,Int.cast_one]
  linear_combination hk

/-- Changing any chart choices changes the full eta representative
by an integer multiple of pi. This also compares opposite half-gaps. -/
theorem representative_sub_eq_int_pi
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    {W' V' U' : Set (CoeffPair p)} {c' : ℤ → ℂ} {T' : ℤ → ℝ}
    {r' R' : ℝ} {z₀' : ℂ} {ρ' : ℝ} {δ' ε' : CoeffPair p → ℂ}
    (D' : SourceAngularEtaAnalyticChartData hp hp1 m s W' V' U' c' T' r' R' z₀' ρ' δ' ε')
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (hψ' : ψ ∈ U') :
    ∃ k : ℤ, sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε ψ-
      sourceAngularEtaCauchyRepresentative hp hp1 m s (c' m) r' R' z₀' ρ' ε' ψ = (k : ℂ)*(Real.pi : ℂ) := by
  have A : SourceAngularComplexDirichletAngleData hp hp1 m univ U δ ε :=
    ⟨D.angle.source_open,subset_univ _,D.angle.halfGap_analytic,D.angle.angle_analytic,
      D.angle.halfGap_ne_zero,D.angle.halfGap_sq,D.angle.terminal_coordinates,D.angle.terminal_root⟩
  have A' : SourceAngularComplexDirichletAngleData hp hp1 m univ U' δ' ε' :=
    ⟨D'.angle.source_open,subset_univ _,D'.angle.halfGap_analytic,D'.angle.angle_analytic,
      D'.angle.halfGap_ne_zero,D'.angle.halfGap_sq,D'.angle.terminal_coordinates,D'.angle.terminal_root⟩
  obtain ⟨k,hk⟩ := A.angle_sub_eq_int_pi A' ψ hψ hψ'
  have hR := D.annulus.etaRemainderCauchyCandidate_eq_on_overlap D'.annulus
    ρ D.inner_lt_cauchy D.cauchy_lt_outer ρ' D'.inner_lt_cauchy D'.cauchy_lt_outer
    ⟨D.angle.source_subset hψ,D'.angle.source_subset hψ'⟩
  refine ⟨k,?_⟩
  simp only [sourceAngularEtaCauchyRepresentative]
  rw [hR]
  linear_combination hk

/-- The chart-independent exponential represents eta modulo pi. -/
theorem exp_two_I_representative_eq
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    {W' V' U' : Set (CoeffPair p)} {c' : ℤ → ℂ} {T' : ℤ → ℝ}
    {r' R' : ℝ} {z₀' : ℂ} {ρ' : ℝ} {δ' ε' : CoeffPair p → ℂ}
    (D' : SourceAngularEtaAnalyticChartData hp hp1 m s W' V' U' c' T' r' R' z₀' ρ' δ' ε')
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (hψ' : ψ ∈ U') :
    Complex.exp (2*Complex.I*sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε ψ) =
      Complex.exp (2*Complex.I*sourceAngularEtaCauchyRepresentative hp hp1 m s (c' m) r' R' z₀' ρ' ε' ψ) := by
  obtain ⟨k,hk⟩ := D.representative_sub_eq_int_pi D' ψ hψ hψ'
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  exact ⟨k,by linear_combination 2*Complex.I*hk⟩

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
