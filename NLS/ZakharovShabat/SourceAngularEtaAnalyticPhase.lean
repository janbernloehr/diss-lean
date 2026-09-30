import NLS.ZakharovShabat.SourceAngularEtaAnalyticChart
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A single analytic phase for eta modulo pi

All full eta charts give the same phase `exp(2i eta)`. Choosing this
unique value gives one source function, analytic and nonzero wherever
an actual open-gap chart exists. Its phase is exactly the phase of
every normalized integrable admissible spectral integral in that chart.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularEtaAnalyticPhaseValues
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : Set ℂ :=
  {z | ∃ W V U : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
    ∃ r R : ℝ, ∃ z₀ : ℂ, ∃ ρ : ℝ, ∃ δ ε : CoeffPair p → ℂ,
      ψ ∈ U ∧ SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε ∧
        Complex.exp (2*Complex.I*sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε ψ) = z}

/-- The unique full eta chart phase, with zero as the unused fallback
at sources where no open-gap chart exists. -/
def sourceAngularEtaAnalyticPhase
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : ℂ := by
  classical
  exact if h : (sourceAngularEtaAnalyticPhaseValues hp hp1 m s ψ).Nonempty then Classical.choose h else 0

namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}

/-- The chart phase is the unique value, without fixing any annulus,
angle branch, or ambient source domain. -/
theorem phaseValues_eq_singleton
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    sourceAngularEtaAnalyticPhaseValues hp hp1 m s ψ =
      {Complex.exp (2*Complex.I*sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε ψ)} := by
  ext z
  constructor
  · rintro ⟨W',V',U',c',T',r',R',z₀',ρ',δ',ε',hψ',D',hz⟩
    exact mem_singleton_iff.mpr (hz.symm.trans (D.exp_two_I_representative_eq D' ψ hψ hψ').symm)
  · intro hz
    exact ⟨W,V,U,c,T,r,R,z₀,ρ,δ,ε,hψ,D,(mem_singleton_iff.mp hz).symm⟩

theorem phase_eq_exp_representative
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    sourceAngularEtaAnalyticPhase hp hp1 m s ψ =
      Complex.exp (2*Complex.I*sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε ψ) := by
  have hne : (sourceAngularEtaAnalyticPhaseValues hp hp1 m s ψ).Nonempty := by
    rw [D.phaseValues_eq_singleton ψ hψ]
    exact singleton_nonempty _
  unfold sourceAngularEtaAnalyticPhase
  rw [dif_pos hne]
  have h := Classical.choose_spec hne
  exact mem_singleton_iff.mp ((D.phaseValues_eq_singleton ψ hψ).subset h)

theorem phase_ne_zero
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) : sourceAngularEtaAnalyticPhase hp hp1 m s ψ ≠ 0 := by
  rw [D.phase_eq_exp_representative ψ hψ]
  exact Complex.exp_ne_zero _

/-- The single phase is analytic, since it agrees with the analytic
chart formula on a source neighborhood of every chart point. -/
theorem analyticOnNhd_phase
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε) :
    AnalyticOnNhd ℂ (sourceAngularEtaAnalyticPhase hp hp1 m s) U := by
  intro ψ hψ
  have heq : (fun χ => Complex.exp (2*Complex.I*
      sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε χ)) =ᶠ[𝓝 ψ]
      sourceAngularEtaAnalyticPhase hp hp1 m s := by
    filter_upwards [D.angle.source_open.mem_nhds hψ] with χ hχ
    exact (D.phase_eq_exp_representative χ hχ).symm
  exact ((analyticAt_const.mul (D.eta_analytic ψ hψ)).cexp').congr heq

/-- The globally chosen phase is the literal eta integral's phase.
Both periodic anchors and singular periodic terminals are covered. -/
theorem exp_two_I_admissible_pathIntegral_eq_phase
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
    Complex.exp (2*Complex.I*sourceAngularPathIntegral m s Q ψ γ) =
      sourceAngularEtaAnalyticPhase hp hp1 m s ψ := by
  rw [D.phase_eq_exp_representative ψ hψ]
  obtain ⟨k,hk⟩ := D.admissible_pathIntegral_sub_representative_eq_int_pi ψ hψ ha Q γ hQ hnorm hγ hint hmodel
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  exact ⟨k,by linear_combination 2*Complex.I*hk⟩

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
