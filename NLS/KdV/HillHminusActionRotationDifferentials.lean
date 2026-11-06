import NLS.KdV.HillHminusActionGardner

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- A physical original L2 germ remains a germ, with an analytic extension,
at all original sources in a neighborhood of its reference. -/
theorem hillHminusPhysicalGerm_eventually_matching_germs
    (q : RealPeriodOneHillPotential) (F : PeriodOneHminusOne → ℂ)
    (f : RealPeriodOneHillPotential → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = f p) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      AnalyticAt ℂ F (hillOriginalHminusSource p.val) ∧
      ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 p,
        F (hillOriginalHminusSource r.val) = f r := by
  have ht : Tendsto (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      (𝓝 q) (𝓝 (hillOriginalHminusSource q.val)) :=
    (hillOriginalHminusSource.continuous.comp continuous_subtype_val).continuousAt
  have hA := ht.eventually hF.eventually_analyticAt
  obtain ⟨V,hVsub,hV,hqV⟩ := _root_.mem_nhds_iff.mp hmatch
  filter_upwards [hA,hV.mem_nhds hqV] with p hp hpV
  exact ⟨hp,Filter.Eventually.mono (hV.mem_nhds hpV) (fun r hr => hVsub hr)⟩

/-- Differentiate the actual physical Cartesian-action rotation law as
an ENTIRE H-minus-one differential. It is not merely a directional
identity along the isospectral curve. -/
theorem hillOriginalCartesian_action_hminus_Gardner_fderiv
    (q : RealPeriodOneHillPotential) (n m : ℕ+)
    (Z J : PeriodOneHminusOne → ℂ)
    (hZ : AnalyticAt ℂ Z (hillOriginalHminusSource q.val))
    (hJ : AnalyticAt ℂ J (hillOriginalHminusSource q.val))
    (hZM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos)
    (hJM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 m 0 : ℂ)) :
    fderiv ℂ (NLS.Poisson.hminusGardnerBracket Z J) (hillOriginalHminusSource q.val) =
      (I * (if (m:ℕ)=(n:ℕ) then 1 else 0 : ℂ)) •
        fderiv ℂ Z (hillOriginalHminusSource q.val) := by
  let c : ℂ := I * (if (m:ℕ)=(n:ℕ) then 1 else 0 : ℂ)
  have hNZ := hillHminusPhysicalGerm_eventually_matching_germs q Z _ hZ hZM
  have hNJ := hillHminusPhysicalGerm_eventually_matching_germs q J _ hJ hJM
  have hB : AnalyticAt ℂ (NLS.Poisson.hminusGardnerBracket Z J) (hillOriginalHminusSource q.val) :=
    (NLS.Poisson.gardnerBivector.analyticAt_bilinear _).comp₂
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hZ.fderiv)
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hJ.fderiv)
  have hreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      NLS.Poisson.hminusGardnerBracket Z J (hillOriginalHminusSource p.val) =
        c * Z (hillOriginalHminusSource p.val) := by
    filter_upwards [hNZ,hNJ,hZM] with p hpZ hpJ hp
    rw [hillOriginalCartesian_action_hminus_Gardner_eq p n m Z J hpZ.1 hpJ.1 hpZ.2 hpJ.2,hp]
  have he := hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq q
    (NLS.Poisson.hminusGardnerBracket Z J) (fun a => c * Z a) hB (analyticAt_const.mul hZ) hreal
  rw [he]
  exact (hZ.differentiableAt.hasFDerivAt.const_mul c).fderiv

end NLS.KdV
