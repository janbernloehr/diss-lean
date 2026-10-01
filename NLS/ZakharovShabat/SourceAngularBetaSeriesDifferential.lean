import NLS.ZakharovShabat.SourceAngularEtaDifferential
import NLS.ZakharovShabat.SourceAngularThetaPoisson
import NLS.Poisson.SourceHamiltonianDirection
import NLS.ComplexAnalysis.LocalAnalyticApproximationOn

/-! # Derivatives and brackets of the actual beta correction series

The actual symmetric beta partial sums converge locally uniformly.
Their full Fréchet derivatives therefore converge in operator norm
on smaller source balls. Finite cotangent sums and their Hamiltonian
evaluations converge to the derivative and bracket of the actual sum.
Adding the actual eta cotangent gives the single theta cotangent and
its bracket as limits of these finite sums.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal symmetric cutoff of the actual beta correction. Its
series term already omits the diagonal. -/
def sourceAngularBetaPartialSum (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (N : ℕ) (ψ : CoeffPair p) : ℂ :=
  ∑ m ∈ Finset.Icc (-(N : ℤ)) N, sourceAngularBetaSeriesTerm hp hp1 n s ψ m

namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

theorem analyticOnNhd_betaSeriesTerm
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s) (n m : ℤ) :
    AnalyticOnNhd ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 n s ψ m) W := by
  classical
  by_cases hmn : m = n
  · simp only [sourceAngularBetaSeriesTerm,if_pos hmn]
    exact analyticOnNhd_const
  · simp only [sourceAngularBetaSeriesTerm,if_neg hmn]
    exact (D.beta_analytic n m hmn).mono D.source_subset

theorem analyticOnNhd_betaPartialSum
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s) (n : ℤ) (N : ℕ) :
    AnalyticOnNhd ℂ (sourceAngularBetaPartialSum hp hp1 n s N) W := by
  intro ψ hψ
  apply Finset.analyticAt_fun_sum
  intro m _
  exact D.analyticOnNhd_betaSeriesTerm n m ψ hψ

/-- The exact full cotangent of a finite actual beta cutoff. -/
theorem fderiv_betaPartialSum_eq_sum
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (N : ℕ) (φ : CoeffPair p) (hφ : φ ∈ W) :
    fderiv ℂ (sourceAngularBetaPartialSum hp hp1 n s N) φ =
      ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        fderiv ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 n s ψ m) φ :=
  fderiv_fun_sum (fun m _ => (D.analyticOnNhd_betaSeriesTerm n m φ hφ).differentiableAt)

/-- The actual beta cutoffs satisfy the Banach holomorphic approximation
criterion on the common source domain. -/
theorem betaCorrection_analyticApproximation
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s) (n : ℤ) :
    HasLocalUniformAnalyticApproximationOn
      (sourceAngularBetaPartialSum hp hp1 n s) (sourceAngularBetaCorrection hp hp1 n s) W := by
  apply HasLocalUniformAnalyticApproximationOn.of_open_local_uniform D.source_open
    (D.analyticOnNhd_betaPartialSum n)
  intro φ hφ
  obtain ⟨V,hV,hφV,_,hconv⟩ := D.beta_series.locally_uniform φ (D.source_subset hφ)
  exact ⟨V,hV,hφV,hconv n⟩

/-- Full Fréchet derivatives of the actual cutoffs converge uniformly in
operator norm on a source ball around every common-domain point. -/
theorem local_uniform_betaCorrection_fderiv
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ r : ℝ, 0 < r ∧ ball φ r ⊆ W ∧
      TendstoUniformlyOn (fun N => fderiv ℂ (sourceAngularBetaPartialSum hp hp1 n s N))
        (fderiv ℂ (sourceAngularBetaCorrection hp hp1 n s)) atTop (ball φ r) :=
  (D.betaCorrection_analyticApproximation n).uniform_fderiv φ hφ

/-- The actual infinite correction cotangent is the operator-norm limit
of the symmetric sums of actual individual beta cotangents. -/
theorem tendsto_betaSeriesCotangents
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : CoeffPair p) (hφ : φ ∈ W) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      fderiv ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 n s ψ m) φ) atTop
        (𝓝 (fderiv ℂ (sourceAngularBetaCorrection hp hp1 n s) φ)) := by
  obtain ⟨r,hr,_,hconv⟩ := D.local_uniform_betaCorrection_fderiv n φ hφ
  exact (hconv.tendsto_at (mem_ball_self hr)).congr'
    (Eventually.of_forall (fun N => D.fderiv_betaPartialSum_eq_sum n N φ hφ))

/-- The derivative may be passed through the actual symmetric beta
series in every source direction, also below the Hilbert exponent. -/
theorem tendsto_betaSeriesVariations
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : CoeffPair p) (hφ : φ ∈ W) (h : CoeffPair p) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      (fderiv ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 n s ψ m) φ) h) atTop
        (𝓝 ((fderiv ℂ (sourceAngularBetaCorrection hp hp1 n s) φ) h)) := by
  have hc : Continuous (fun L : CoeffPair p →L[ℂ] ℂ => L h) := by fun_prop
  simpa only [Function.comp_def,sum_apply] using
    hc.continuousAt.tendsto.comp (D.tendsto_betaSeriesCotangents n φ hφ)

/-- Every Hamiltonian bracket of the actual correction is the limit
of its finite actual beta bracket sums. -/
theorem tendsto_betaSeriesBrackets
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (G : CoeffPair p → ℂ)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      sourceBracket h2p (fun ψ => sourceAngularBetaSeriesTerm hp hp1 n s ψ m) G φ) atTop
        (𝓝 (sourceBracket h2p (sourceAngularBetaCorrection hp hp1 n s) G φ)) := by
  simpa only [fderiv_apply_sourceHamiltonianVector] using
    D.tendsto_betaSeriesVariations n φ hφ (sourceHamiltonianVector h2p G φ)

/-- The actual theta cotangent is the limit of eta plus the symmetric
finite beta cotangent sums, independently of the local eta chart. -/
theorem tendsto_thetaSeriesCotangents
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s) (n : ℤ)
    {V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}
    (C : SourceAngularEtaAnalyticChartData hp hp1 n s B V U c T r R z₀ ρ δ ε)
    (hUW : U ⊆ W) (φ : CoeffPair p) (hφ : φ ∈ U) :
    Tendsto (fun N : ℕ => sourceAngularEtaDifferential hp hp1 n s φ+
      ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        fderiv ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 n s ψ m) φ) atTop
          (𝓝 (sourceAngularThetaDifferential hp hp1 n s φ)) := by
  have ht := (tendsto_const_nhds (x := sourceAngularEtaDifferential hp hp1 n s φ)).add
    (D.tendsto_betaSeriesCotangents n φ (hUW hφ))
  rw [← C.thetaDifferential_eq_eta_add_betaCorrection
    ((D.beta_series.analytic_correction n).mono (hUW.trans D.source_subset)) φ hφ] at ht
  exact ht

/-- Every source-direction variation of the actual theta cotangent is
the limit of eta plus the symmetric finite beta variations. -/
theorem tendsto_thetaSeriesVariations
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s) (n : ℤ)
    {V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}
    (C : SourceAngularEtaAnalyticChartData hp hp1 n s B V U c T r R z₀ ρ δ ε)
    (hUW : U ⊆ W) (φ : CoeffPair p) (hφ : φ ∈ U) (h : CoeffPair p) :
    Tendsto (fun N : ℕ => sourceAngularEtaDifferential hp hp1 n s φ h +
      ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        (fderiv ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 n s ψ m) φ) h) atTop
          (𝓝 (sourceAngularThetaDifferential hp hp1 n s φ h)) := by
  have hc : Continuous (fun L : CoeffPair p →L[ℂ] ℂ => L h) := by fun_prop
  simpa only [Function.comp_def,add_apply,sum_apply] using
    hc.continuousAt.tendsto.comp (D.tendsto_thetaSeriesCotangents n C hUW φ hφ)

/-- The actual angle/functional bracket is the limit of the diagonal
eta contribution plus the actual finite beta bracket sums. -/
theorem tendsto_thetaSeriesBrackets
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (G : CoeffPair p → ℂ)
    {V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}
    (C : SourceAngularEtaAnalyticChartData hp hp1 n s B V U c T r R z₀ ρ δ ε)
    (hUW : U ⊆ W) (φ : CoeffPair p) (hφ : φ ∈ U) :
    Tendsto (fun N : ℕ => sourceBivector h2p (sourceAngularEtaDifferential hp hp1 n s φ)
      (fderiv ℂ G φ)+∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        sourceBracket h2p (fun ψ => sourceAngularBetaSeriesTerm hp hp1 n s ψ m) G φ) atTop
          (𝓝 (sourceAngularThetaFunctionalBracket hp hp1 h2p n s G φ)) := by
  simpa only [sourceHamiltonianVector,apply_sourceHamiltonianDirection,sourceBracket,
    sourceAngularThetaFunctionalBracket] using
    D.tendsto_thetaSeriesVariations n C hUW φ hφ (sourceHamiltonianVector h2p G φ)

/-- Both angle cotangents may be approximated simultaneously in their
actual bracket. The two finite beta sums use the same symmetric cutoff. -/
theorem tendsto_thetaThetaSeriesBrackets
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ)
    {Vn Un Vm Um : Set (CoeffPair p)} {cn cm : ℤ → ℂ} {Tn Tm : ℤ → ℝ}
    {rn Rn rm Rm : ℝ} {zn zm : ℂ} {ρn ρm : ℝ}
    {δn εn δm εm : CoeffPair p → ℂ}
    (Cn : SourceAngularEtaAnalyticChartData hp hp1 n s B Vn Un cn Tn rn Rn zn ρn δn εn)
    (Cm : SourceAngularEtaAnalyticChartData hp hp1 m s B Vm Um cm Tm rm Rm zm ρm δm εm)
    (hnW : Un ⊆ W) (hmW : Um ⊆ W) (φ : CoeffPair p) (hφn : φ ∈ Un) (hφm : φ ∈ Um) :
    Tendsto (fun N : ℕ => sourceBivector h2p
      (sourceAngularEtaDifferential hp hp1 n s φ +
        ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
          fderiv ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 n s ψ j) φ)
      (sourceAngularEtaDifferential hp hp1 m s φ +
        ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
          fderiv ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 m s ψ j) φ)) atTop
      (𝓝 (sourceAngularThetaThetaBracket hp hp1 h2p n m s φ)) := by
  have hc : Continuous (fun q : (CoeffPair p →L[ℂ] ℂ) × (CoeffPair p →L[ℂ] ℂ) =>
    sourceBivector h2p q.1 q.2) := by fun_prop
  simpa only [Function.comp_def,sourceAngularThetaThetaBracket] using
    hc.continuousAt.tendsto.comp
      ((D.tendsto_thetaSeriesCotangents n Cn hnW φ hφn).prodMk_nhds
        (D.tendsto_thetaSeriesCotangents m Cm hmW φ hφm))

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
