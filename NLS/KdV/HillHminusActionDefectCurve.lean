import NLS.KdV.HillHminusCartesianDefectEvolution

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- An actual original action has a genuine H-minus-one analytic physical
germ at EVERY positive index, including low and closed gaps. -/
theorem exists_hillOriginal_action_hminus_physical_germ
    (q : RealPeriodOneHillPotential) (k : ℕ+) :
    ∃ J : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ J (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 k 0 : ℂ) := by
  obtain ⟨U,_,hqU,hJ,_⟩ := exists_hillHminusRelativeAction_analytic_neighborhood
    q.val q.property.1 q.property.2 k k.pos
  obtain ⟨V,hV,hqV,hM⟩ := exists_hillHminusRelativeAction_original_matching q k k.pos
  exact ⟨hillHminusRelativeAction q.val q.property.1 q.property.2 k,hJ _ hqU,
    Filter.Eventually.mono (hV.mem_nhds hqV) (fun p hp => hM p hp)⟩

/-- The FULL original Cartesian matrix defect satisfies its actual
homogeneous ODE on every original physical action trajectory. All germ
and action Hamiltonian data are constructed or physically matched. -/
theorem hasDerivAt_hillActionCurve_cartesian_matrix_defect
    (n m k : ℕ+) (σ τ : Bool) (γ : ℝ → RealPeriodOneHillPotential) (t : ℝ)
    (hγ : HasDerivAt (fun s => (γ s).val)
      (hillPhysicalMomentHamiltonianSource (γ t).val (γ t).property.1 (γ t).property.2 k k.pos 0) t)
    (hgapn : hillRealGapHalfLength (γ t).val (γ t).property.1 (γ t).property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength (γ t).val (γ t).property.1 (γ t).property.2 m ≠ 0)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource (γ t).val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource (γ t).val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (γ t),
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (γ t),
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian τ m p) :
    HasDerivAt (fun s => NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource (γ s).val) -
        hillOriginalComplexGardnerMatrixEntry σ τ n m)
      (-(hillCartesianActionRotationWeight σ n k + hillCartesianActionRotationWeight τ m k) *
        (NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource (γ t).val) -
          hillOriginalComplexGardnerMatrixEntry σ τ n m)) t := by
  obtain ⟨J,hJ,hJM⟩ := exists_hillOriginal_action_hminus_physical_germ (γ t) k
  have hB : AnalyticAt ℂ (NLS.Poisson.hminusGardnerBracket F G) (hillOriginalHminusSource (γ t).val) :=
    (NLS.Poisson.gardnerBivector.analyticAt_bilinear _).comp₂
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hF.fderiv)
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hG.fderiv)
  have hD : AnalyticAt ℂ (fun a => NLS.Poisson.hminusGardnerBracket F G a -
      hillOriginalComplexGardnerMatrixEntry σ τ n m) (hillOriginalHminusSource (γ t).val) :=
    hB.sub analyticAt_const
  let P := hillOriginalHminusSource.restrictScalars ℝ
  have hd := (hD.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (P.hasFDerivAt.comp_hasDerivAt t hγ)
  change HasDerivAt
    (fun s => NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource (γ s).val) -
      hillOriginalComplexGardnerMatrixEntry σ τ n m)
    ((fderiv ℂ (fun a => NLS.Poisson.hminusGardnerBracket F G a -
        hillOriginalComplexGardnerMatrixEntry σ τ n m) (hillOriginalHminusSource (γ t).val))
      (hillOriginalHminusSource (hillPhysicalMomentHamiltonianSource
        (γ t).val (γ t).property.1 (γ t).property.2 k k.pos 0))) t at hd
  rw [hillSignedCartesian_matrix_defect_action_evolution (γ t) n m k σ τ hgapn hgapm
    F G J hF hG hJ hFM hGM hJM] at hd
  exact hd

end NLS.KdV
