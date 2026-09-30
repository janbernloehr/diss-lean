import NLS.ZakharovShabat.SourceAngularThetaSpectral
import NLS.ZakharovShabat.SourceAngularEtaTheorem13_1Analytic

/-! # Theorem 13.1(iv) on the actual common source neighborhood

The same normalized psi family carries all beta estimates, its analytic
correction series, and eta modulo pi. Every real off-diagonal beta and
the full correction are real. Theta has constructed analytic real
representatives, agreeing modulo pi, and a single analytic nonzero phase
on each indexed open-gap domain. That phase has unit norm on the real
source locus. Literal normalized integrable spectral formulas are supplied
by `SourceAngularThetaSpectral`.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceAngularThetaCommonDomainData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W₀ B W : Set (CoeffPair p))
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) : Prop
    extends SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s where
  source_open : IsOpen W
  real_subset : realTypeSourceLocus p ⊆ W
  source_subset : W ⊆ B
  beta_real : ∀ ψ ∈ W, IsRealType (CoeffPair.toMax p ψ) →
    ∀ n m : ℤ, m ≠ n → (sourceAngularBeta hp hp1 n m s ψ).im = 0
  correction_real : ∀ ψ ∈ W, IsRealType (CoeffPair.toMax p ψ) →
    ∀ n : ℤ, (sourceAngularBetaCorrection hp hp1 n s ψ).im = 0
  open_gap : ∀ n : ℤ, IsOpen {ψ : CoeffPair p | ψ ∈ W ∧
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0}
  eta_phase_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceAngularEtaAnalyticPhase hp hp1 n s)
    {ψ : CoeffPair p | ψ ∈ W ∧ canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0}
  theta_phase_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceAngularThetaAnalyticPhase hp hp1 n s)
    {ψ : CoeffPair p | ψ ∈ W ∧ canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0}
  theta_phase_ne_zero : ∀ ψ ∈ W, ∀ n : ℤ, canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 →
      sourceAngularThetaAnalyticPhase hp hp1 n s ψ ≠ 0
  theta_phase_norm_real : ∀ ψ ∈ W, IsRealType (CoeffPair.toMax p ψ) → ∀ n : ℤ,
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 →
      ‖sourceAngularThetaAnalyticPhase hp hp1 n s ψ‖ = 1
  local_charts : ∀ n : ℤ, ∀ φ ∈ W, canonicalPeriodicGap hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0 →
      ∃ V U : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
        ∃ r R : ℝ, ∃ z₀ : ℂ, ∃ ρ : ℝ, ∃ δ ε : CoeffPair p → ℂ,
          φ ∈ U ∧ U ⊆ W ∧
          δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n/2 ∧
          SourceAngularEtaAnalyticChartData hp hp1 n s B V U c T r R z₀ ρ δ ε

/-- Every complex open-gap source has a constructed analytic theta
representative, real at every real source in its chart. -/
theorem SourceAngularThetaCommonDomainData.exists_local_analytic_real_representative
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : CoeffPair p) (hφ : φ ∈ W)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0) :
    ∃ V U : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
      ∃ r R : ℝ, ∃ z₀ : ℂ, ∃ ρ : ℝ, ∃ δ ε : CoeffPair p → ℂ,
        φ ∈ U ∧ U ⊆ W ∧
        SourceAngularEtaAnalyticChartData hp hp1 n s B V U c T r R z₀ ρ δ ε ∧
        AnalyticOnNhd ℂ (sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε) U ∧
        ∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) →
          (sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ).im = 0 := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,_,E⟩ := D.local_charts n φ hφ hgap
  exact ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,E,
    E.theta_representative_analytic ((D.beta_series.analytic_correction n).mono (hUW.trans D.source_subset)),
    fun ψ hψ hreal => E.theta_representative_im_eq_zero_of_realType
      D.psi.toSourcePsiIsolatingComplexExtension ψ hψ hreal (D.correction_real ψ (hUW hψ) hreal n)⟩

/-- Theorem 13.1(iv) retains the full results of (i), (ii), and (iii).
No angular primitives, summability, or reality assumptions are inputs. -/
theorem exists_sourceAngularTheta_theorem13_1_iv (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen B ∧ realTypeSourceLocus p ⊆ B ∧ B ⊆ W₀ ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        SourceAngularThetaCommonDomainData hp hp1 W₀ B W s := by
  obtain ⟨W₀,B,W,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,hW,hWreal,hWB,s,D,hcharts⟩ :=
    exists_sourceAngularEta_theorem13_1_ii hp hp1
  have hbeta (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ))
      (n m : ℤ) (hmn : m ≠ n) : (sourceAngularBeta hp hp1 n m s ψ).im = 0 := by
    by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = 0
    · have hd : sourcePeriodicGapDisplacement hp hp1 ψ m = 0 := by
        rw [sourcePeriodicGapDisplacement_apply,hgap]
      rw [sourceAngularBeta_eq_zero_of_real_collapsed_gap hp hp1 n m s ψ hreal hd]
      rfl
    · obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hψU,_,_,E⟩ := (hcharts m).2.2.2 ψ hψ hgap
      exact E.beta_im_eq_zero_of_realType D.psi.toSourcePsiIsolatingComplexExtension ψ hψU hreal n hmn
  have hcorrection (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
      (sourceAngularBetaCorrection hp hp1 n s ψ).im = 0 :=
    D.beta_series.toSourceAngularBetaSeriesAnalyticData.correction_im_eq_zero_of_terms ψ (hWB hψ) n
      (hbeta ψ hψ hreal n)
  refine ⟨W₀,B,W,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,s,{
    toSourceAngularEtaLocalCommonDomainData := D
    source_open := hW
    real_subset := hWreal
    source_subset := hWB
    beta_real := hbeta
    correction_real := hcorrection
    open_gap := fun n => (hcharts n).1
    eta_phase_analytic := fun n => (hcharts n).2.1
    theta_phase_analytic := ?_
    theta_phase_ne_zero := ?_
    theta_phase_norm_real := ?_
    local_charts := fun n => (hcharts n).2.2.2
  }⟩
  · intro n ψ hψ
    exact ((hcharts n).2.1 ψ hψ).mul
      ((analyticAt_const.mul (D.beta_series.analytic_correction n ψ (hWB hψ.1))).cexp')
  · intro ψ hψ n hgap
    exact mul_ne_zero ((hcharts n).2.2.1 ψ hψ hgap) (Complex.exp_ne_zero _)
  · intro ψ hψ hreal n hgap
    obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hψU,_,_,E⟩ := (hcharts n).2.2.2 ψ hψ hgap
    exact E.theta_phase_norm_eq_one_of_realType D.psi.toSourcePsiIsolatingComplexExtension ψ hψU hreal
      (hcorrection ψ hψ hreal n)

end NLS.ZakharovShabat
