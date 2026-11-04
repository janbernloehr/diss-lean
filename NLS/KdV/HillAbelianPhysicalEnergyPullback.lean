import NLS.KdV.HillAbelianFrequencyDifferentials
import NLS.KdV.HillHminusOneMiuraAllLabels

/-! The Abelian frequency forms are the ACTUAL physical energy
differentials with the exact 2*z Jacobian, including real band values.
Their endpoint energies are the ORIGINAL low/high Hill labels. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillHminusDirichletBall

theorem positive_frequency_energy_mem_domain (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A) (z : ℂ) (hz : 0 < z.re)
    (hroot : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (hillMiuraDiagonal (B.miuraBall.actionBall.lift q))) :
    (z^2-(B.miuraBall.actionBall.shift:ℂ),q) ∈ B.energyDomain A := by
  refine ⟨⟨mem_univ _,hq⟩,hq.2,?_,?_⟩
  · simpa only [energyCoordinates,sub_add_cancel] using sq_mem_slitPlane_of_re_pos z hz
  · simpa only [energyCoordinates,sub_add_cancel,sqrt_sq_of_re_pos z hz] using hroot

theorem canonical_root_at_positive_frequency_of_real (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : 0 < z.re)
    (hroot : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (hillMiuraDiagonal (B.miuraBall.actionBall.lift q))) :
    hillHminusCanonicalEnergyRoot (z^2-(B.miuraBall.actionBall.shift:ℂ),q) =
      sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal (B.miuraBall.actionBall.lift q)) z := by
  have hlocal := B.positive_frequency_energy_mem_domain A q hq z hz hroot
  rw [hillHminusCanonicalEnergyRoot_eq_local_of_real B A _ q hr hlocal]
  exact hillHminusMiuraRoot_at_squared_energy _ _ z hz

end NLS.KdV.HillHminusDirichletBall

namespace NLS.KdV.HillProductEquationPatch


theorem abelianFrequencyDifferential_physical_energy_pullback (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : 0 < z.re)
    (hroot : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi q)) :
    (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q) ∈ hillHminusCanonicalEnergyRootDomain ∧
      ∀ n : ℕ+, P.abelianFrequencyDifferential n (z,q) = 2*z*hillHminusCanonicalEnergyDifferential n
        (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q) := by
  have hpsi : q ∈ P.parent.parent.psiSource P.parent.family := P.parent.subset (P.subset hq)
  have hlocal := P.parent.parent.positive_frequency_energy_mem_domain P.parent.family q hpsi z hz hroot
  have heq := P.parent.parent.canonical_root_at_positive_frequency_of_real P.parent.family q hpsi hr z hz hroot
  refine ⟨real_mem_hillHminusCanonicalEnergyRootDomain_of_local P.parent.parent P.parent.family _ q hr hlocal,?_⟩
  intro n
  rw [abelianFrequencyDifferential,abelianFrequencyNumerator,hillHminusCanonicalEnergyDifferential,heq]
  dsimp only [sourcePsi]
  ring

theorem abelianGapDisc_re_pos_of_real (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) : 0 < z.re := by
  have hp := P.positive_circle_left_of_real q hq hr m
  have hb := re_bounds_of_mem_realCenteredClosedBall (ball_subset_closedBall hz)
  linarith [hb.1]

theorem abelian_gap_endpoint_energies_eq_original_labels (P : HillProductEquationPatch)
    (m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    (canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))^2-
        (P.parent.parent.miuraBall.actionBall.shift:ℂ) = (hillHminusLabels q hr (2*(m:ℕ)-1):ℂ) ∧
      (canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))^2-
        (P.parent.parent.miuraBall.actionBall.shift:ℂ) = (hillHminusLabels q hr (2*(m:ℕ)):ℂ) := by
  let B := P.parent.parent.miuraBall.actionBall
  have hqB := (P.parent.subset (P.subset hq)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hqB hr⟩
  have he := hillHminusLabels_pair_eq_squared_miuraDirac q hr u B.shift (B.image q hqB) (B.outside q hqB) (m:ℕ) m.pos
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) ((m:ℕ):ℤ)
  have hl : ((hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re:ℂ) = hillMiuraDiracLeft u.val ((m:ℕ):ℤ) := by
    apply Complex.ext
    · simp
    · exact him.1.symm
  have hu : ((hillMiuraDiracRight u.val ((m:ℕ):ℤ)).re:ℂ) = hillMiuraDiracRight u.val ((m:ℕ):ℤ) := by
    apply Complex.ext
    · simp
    · exact him.2.symm
  constructor
  · have h := congrArg (fun x : ℝ => (x:ℂ)) he.1
    push_cast at h
    rw [hl] at h
    exact h.symm
  · have h := congrArg (fun x : ℝ => (x:ℂ)) he.2
    push_cast at h
    rw [hu] at h
    exact h.symm

end NLS.KdV.HillProductEquationPatch
