import NLS.KdV.HillHminusPhysicalGermBrackets
import NLS.KdV.HillHminusCartesianGerms

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- The ACTUAL physical Cartesian Gardner bracket passes through every
strongly H-minus-one convergent ORIGINAL isospectral sequence, for open
selected gaps. Arbitrary physically matched analytic representatives at
EVERY point give the same limit. No L2 convergence is assumed. -/
theorem hillOriginalCartesianGerms_hminus_Gardner_tendsto
    (q : RealPeriodOneHillPotential) (n m : ℕ+)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (p : ℕ → RealPeriodOneHillPotential)
    (hΔ : ∀ j E, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E =
      hillL2Discriminant (SpectralWeight.one.toCoeff (p j).val) E)
    (hp : Tendsto (fun j => hillOriginalHminusSource (p j).val) atTop
      (𝓝 (hillOriginalHminusSource q.val)))
    (F0 G0 : PeriodOneHminusOne → ℂ) (F G : ℕ → PeriodOneHminusOne → ℂ)
    (hF0 : AnalyticAt ℂ F0 (hillOriginalHminusSource q.val))
    (hG0 : AnalyticAt ℂ G0 (hillOriginalHminusSource q.val))
    (hF : ∀ j, AnalyticAt ℂ (F j) (hillOriginalHminusSource (p j).val))
    (hG : ∀ j, AnalyticAt ℂ (G j) (hillOriginalHminusSource (p j).val))
    (hF0M : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q,
      F0 (hillOriginalHminusSource r.val) = hillSpectralCartesian r.val r.property.1 r.property.2 n n.pos)
    (hG0M : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q,
      G0 (hillOriginalHminusSource r.val) = hillSpectralCartesian r.val r.property.1 r.property.2 m m.pos)
    (hFM : ∀ j, ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (p j),
      F j (hillOriginalHminusSource r.val) = hillSpectralCartesian r.val r.property.1 r.property.2 n n.pos)
    (hGM : ∀ j, ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (p j),
      G j (hillOriginalHminusSource r.val) = hillSpectralCartesian r.val r.property.1 r.property.2 m m.pos) :
    Tendsto (fun j => NLS.Poisson.hminusGardnerBracket (F j) (G j)
        (hillOriginalHminusSource (p j).val)) atTop
      (𝓝 (NLS.Poisson.hminusGardnerBracket F0 G0 (hillOriginalHminusSource q.val))) := by
  obtain ⟨ε,hε,Z,hZ,hZM⟩ :=
    exists_hillOriginal_cartesian_hminus_isospectral_physical_germs q n hgapn
  obtain ⟨δ,hδ,W,hW,hWM⟩ :=
    exists_hillOriginal_cartesian_hminus_isospectral_physical_germs q m hgapm
  let U := ball (hillOriginalHminusSource q.val) ε ∩ ball (hillOriginalHminusSource q.val) δ
  have hqU : hillOriginalHminusSource q.val ∈ U := ⟨mem_ball_self hε,mem_ball_self hδ⟩
  have hZU : AnalyticOnNhd ℂ Z U := hZ.mono inter_subset_left
  have hWU : AnalyticOnNhd ℂ W U := hW.mono inter_subset_right
  have hB := NLS.Poisson.analyticOnNhd_hminusGardnerBracket Z W hZU hWU
  have hconv := (hB _ hqU).continuousAt.tendsto.comp hp
  have hnear : ∀ᶠ j in atTop, hillOriginalHminusSource (p j).val ∈ U :=
    hp.eventually ((isOpen_ball.inter isOpen_ball).mem_nhds hqU)
  have hZq : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q,
      Z (hillOriginalHminusSource r.val) = hillSpectralCartesian r.val r.property.1 r.property.2 n n.pos := by
    obtain ⟨V,hV,hq,hmatch⟩ := hZM q hqU.1 (fun _ => rfl)
    exact Filter.Eventually.mono (hV.mem_nhds hq) (fun r hr => hmatch r hr)
  have hWq : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q,
      W (hillOriginalHminusSource r.val) = hillSpectralCartesian r.val r.property.1 r.property.2 m m.pos := by
    obtain ⟨V,hV,hq,hmatch⟩ := hWM q hqU.2 (fun _ => rfl)
    exact Filter.Eventually.mono (hV.mem_nhds hq) (fun r hr => hmatch r hr)
  have he0 := hillHminusPhysicalGerm_Gardner_eq_of_eventuallyEq q F0 G0 Z W
    hF0 hG0 (hZU _ hqU) (hWU _ hqU)
    (by filter_upwards [hF0M,hZq] with r hr hz; exact hr.trans hz.symm)
    (by filter_upwards [hG0M,hWq] with r hr hw; exact hr.trans hw.symm)
  rw [he0]
  apply hconv.congr'
  filter_upwards [hnear] with j hj
  obtain ⟨V,hV,hpj,hZp⟩ := hZM (p j) hj.1 (hΔ j)
  obtain ⟨T,hT,hpjT,hWp⟩ := hWM (p j) hj.2 (hΔ j)
  have hZj : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (p j),
      Z (hillOriginalHminusSource r.val) = hillSpectralCartesian r.val r.property.1 r.property.2 n n.pos :=
    Filter.Eventually.mono (hV.mem_nhds hpj) (fun r hr => hZp r hr)
  have hWj : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (p j),
      W (hillOriginalHminusSource r.val) = hillSpectralCartesian r.val r.property.1 r.property.2 m m.pos :=
    Filter.Eventually.mono (hT.mem_nhds hpjT) (fun r hr => hWp r hr)
  exact (hillHminusPhysicalGerm_Gardner_eq_of_eventuallyEq (p j) (F j) (G j) Z W
    (hF j) (hG j) (hZU _ hj) (hWU _ hj)
    (by filter_upwards [hFM j,hZj] with r hr hz; exact hr.trans hz.symm)
    (by filter_upwards [hGM j,hWj] with r hr hw; exact hr.trans hw.symm)).symm

end NLS.KdV
