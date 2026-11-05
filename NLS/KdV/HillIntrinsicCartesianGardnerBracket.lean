import NLS.KdV.HillHminusNormalizedIndexedStationarity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- A genuine analytic germ of each ORIGINAL signed Cartesian at its
own open gap, with matching on an ORIGINAL real L2 neighborhood. -/
theorem exists_hillSignedCartesian_hminus_physical_germ
    (q : RealPeriodOneHillPotential) (n : ℕ+) (σ : Bool)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ∃ F : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ F (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p := by
  obtain ⟨ε,hε,F,hF,hM⟩ := exists_hillSignedCartesian_hminus_isospectral_physical_germs q n σ hgap
  obtain ⟨V,hV,hqV,hVM⟩ := hM q (mem_ball_self hε) (fun _ => rfl)
  exact ⟨F,hF _ (mem_ball_self hε),Filter.Eventually.mono (hV.mem_nhds hqV) (fun p hp => hVM p hp)⟩

/-- A representative of the ORIGINAL physical germ; the bracket below
is independent of this choice at every open selected gap. -/
def hillSignedCartesianHminusGerm (q : RealPeriodOneHillPotential) (n : ℕ+) (σ : Bool) :
    PeriodOneHminusOne → ℂ :=
  if hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0 then
    Classical.choose (exists_hillSignedCartesian_hminus_physical_germ q n σ hgap)
  else 0

theorem hillSignedCartesianHminusGerm_spec
    (q : RealPeriodOneHillPotential) (n : ℕ+) (σ : Bool)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    AnalyticAt ℂ (hillSignedCartesianHminusGerm q n σ) (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        hillSignedCartesianHminusGerm q n σ (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p := by
  simpa only [hillSignedCartesianHminusGerm,dif_pos hgap] using
    Classical.choose_spec (exists_hillSignedCartesian_hminus_physical_germ q n σ hgap)

/-- The intrinsic ORIGINAL Cartesian bracket, using the genuine physical
germ. Its open-gap value is independent of any chosen representative. -/
def hillIntrinsicCartesianGardnerBracket (n m : ℕ+) (σ τ : Bool) (q : RealPeriodOneHillPotential) : ℂ :=
  NLS.Poisson.hminusGardnerBracket (hillSignedCartesianHminusGerm q n σ)
    (hillSignedCartesianHminusGerm q m τ) (hillOriginalHminusSource q.val)

def hillIntrinsicNormalizedCartesianBracket (n m : ℕ+) (σ τ : Bool) (q : RealPeriodOneHillPotential) : ℂ :=
  hillIntrinsicCartesianGardnerBracket n m σ τ q /
    (hillSignedSpectralCartesian σ n q * hillSignedSpectralCartesian τ m q)

theorem hillIntrinsicCartesianGardnerBracket_eq_of_physical_germs
    (q : RealPeriodOneHillPotential) (n m : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian τ m p) :
    hillIntrinsicCartesianGardnerBracket n m σ τ q =
      NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource q.val) := by
  obtain ⟨hZ,hZM⟩ := hillSignedCartesianHminusGerm_spec q n σ hgapn
  obtain ⟨hW,hWM⟩ := hillSignedCartesianHminusGerm_spec q m τ hgapm
  exact hillHminusPhysicalGerm_Gardner_eq_of_eventuallyEq q _ _ F G hZ hW hF hG
    (by filter_upwards [hZM,hFM] with p hp hf; exact hp.trans hf.symm)
    (by filter_upwards [hWM,hGM] with p hp hg; exact hp.trans hg.symm)

/-- A pair of ORIGINAL physical germs gives a single analytic formula
for the intrinsic normalized bracket throughout an ORIGINAL L2 neighborhood. -/
theorem hillIntrinsicNormalizedCartesianBracket_eventually_eq_germs
    (q : RealPeriodOneHillPotential) (n m : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian τ m p) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      hillIntrinsicNormalizedCartesianBracket n m σ τ p =
        NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource p.val) /
          (F (hillOriginalHminusSource p.val)*G (hillOriginalHminusSource p.val)) := by
  have hn := (continuous_hillRealGapHalfLength n).continuousAt.eventually_ne hgapn
  have hm := (continuous_hillRealGapHalfLength m).continuousAt.eventually_ne hgapm
  have hNF := hillHminusPhysicalGerm_eventually_matching_germs q F _ hF hFM
  have hNG := hillHminusPhysicalGerm_eventually_matching_germs q G _ hG hGM
  filter_upwards [hn,hm,hNF,hNG,hFM,hGM] with p hpn hpm hpF hpG hpFM hpGM
  rw [hillIntrinsicNormalizedCartesianBracket,
    hillIntrinsicCartesianGardnerBracket_eq_of_physical_germs p n m σ τ hpn hpm F G
      hpF.1 hpG.1 hpF.2 hpG.2,hpFM,hpGM]

end NLS.KdV
