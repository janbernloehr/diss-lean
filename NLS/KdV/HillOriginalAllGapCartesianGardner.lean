import NLS.KdV.HillHminusOriginalAllGapConjugateGerms
import NLS.KdV.HillHminusActionRotationDifferentials
import NLS.KdV.HillHminusSignedCartesianGardnerLimits

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- BOTH literal ORIGINAL complex Cartesian components admit genuine
analytic H-minus-one germs at EVERY original real source and positive
index. No selected-gap openness condition is imposed. -/
theorem exists_hillOriginal_signedCartesian_hminus_physical_germ_all_gaps
    (q : RealPeriodOneHillPotential) (n : ℕ+) (σ : Bool) :
    ∃ Z : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ Z (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        Z (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p := by
  cases σ
  · simpa only [hillSignedSpectralCartesian,Bool.false_eq_true,if_false] using
      exists_hillOriginal_conjugateCartesian_hminus_physical_germ_all_gaps q n
  · simpa only [hillSignedSpectralCartesian,if_true] using
      exists_hillOriginal_cartesian_hminus_physical_germ_all_gaps q n

def hillOriginalSignedCartesianHminusGerm (q : RealPeriodOneHillPotential) (n : ℕ+) (σ : Bool) :
    PeriodOneHminusOne → ℂ :=
  Classical.choose (exists_hillOriginal_signedCartesian_hminus_physical_germ_all_gaps q n σ)

theorem hillOriginalSignedCartesianHminusGerm_spec
    (q : RealPeriodOneHillPotential) (n : ℕ+) (σ : Bool) :
    AnalyticAt ℂ (hillOriginalSignedCartesianHminusGerm q n σ) (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        hillOriginalSignedCartesianHminusGerm q n σ (hillOriginalHminusSource p.val) =
          hillSignedSpectralCartesian σ n p :=
  Classical.choose_spec (exists_hillOriginal_signedCartesian_hminus_physical_germ_all_gaps q n σ)

/-- The ORIGINAL physical Cartesian Gardner entry at ALL sources,
including closed selected gaps. Every representative is a genuine
physical germ, and the resulting bracket is independent of that choice. -/
def hillOriginalCartesianGardnerEntry (n m : ℕ+) (σ τ : Bool) (q : RealPeriodOneHillPotential) : ℂ :=
  NLS.Poisson.hminusGardnerBracket (hillOriginalSignedCartesianHminusGerm q n σ)
    (hillOriginalSignedCartesianHminusGerm q m τ) (hillOriginalHminusSource q.val)

theorem hillOriginalCartesianGardnerEntry_eq_of_physical_germs
    (q : RealPeriodOneHillPotential) (n m : ℕ+) (σ τ : Bool)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian τ m p) :
    hillOriginalCartesianGardnerEntry n m σ τ q =
      NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource q.val) := by
  obtain ⟨hZ,hZM⟩ := hillOriginalSignedCartesianHminusGerm_spec q n σ
  obtain ⟨hW,hWM⟩ := hillOriginalSignedCartesianHminusGerm_spec q m τ
  exact hillHminusPhysicalGerm_Gardner_eq_of_eventuallyEq q _ _ F G hZ hW hF hG
    (by filter_upwards [hZM,hFM] with p hp hf; exact hp.trans hf.symm)
    (by filter_upwards [hWM,hGM] with p hp hg; exact hp.trans hg.symm)

/-- Every actual four-entry ORIGINAL Cartesian Gardner bracket is
continuous in the ORIGINAL L2 topology through closed selected gaps. -/
theorem continuous_hillOriginalCartesianGardnerEntry (n m : ℕ+) (σ τ : Bool) :
    Continuous (hillOriginalCartesianGardnerEntry n m σ τ) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨F,hF,hFM⟩ := exists_hillOriginal_signedCartesian_hminus_physical_germ_all_gaps q n σ
  obtain ⟨G,hG,hGM⟩ := exists_hillOriginal_signedCartesian_hminus_physical_germ_all_gaps q m τ
  have hB : AnalyticAt ℂ (NLS.Poisson.hminusGardnerBracket F G) (hillOriginalHminusSource q.val) :=
    (NLS.Poisson.gardnerBivector.analyticAt_bilinear _).comp₂
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hF.fderiv)
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hG.fderiv)
  have hc : ContinuousAt (fun p : RealPeriodOneHillPotential =>
      NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource p.val)) q :=
    hB.continuousAt.comp (f := fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      (hillOriginalHminusSource.continuous.comp continuous_subtype_val).continuousAt
  apply hc.congr_of_eventuallyEq
  have hNF := hillHminusPhysicalGerm_eventually_matching_germs q F _ hF hFM
  have hNG := hillHminusPhysicalGerm_eventually_matching_germs q G _ hG hGM
  filter_upwards [hNF,hNG] with p hpF hpG
  exact hillOriginalCartesianGardnerEntry_eq_of_physical_germs p n m σ τ F G hpF.1 hpG.1 hpF.2 hpG.2

end NLS.KdV
