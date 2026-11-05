import NLS.KdV.HillMiuraCoefficientContinuity
import NLS.KdV.HillHminusOneMiuraOutsideShift

/-! A uniformly exterior Hill energy shift keeps the central Dirac gap
uniformly open, including under bounded coefficient limits of Miura lifts. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem hillMiura_central_right_ge_one_of_shifted_image
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (B c : ℝ) (hq : ‖q‖ ≤ B)
    (hc : singularHillLowerBoundConstant B+1 ≤ c)
    (himage : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    1 ≤ (hillMiuraDiracRight u.val 0).re := by
  let r := hillMiuraDiracRight u.val 0
  have hr : r.im=0 :=
    (canonicalPeriodicEndpoints_im_eq_zero_of_realType (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
      (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) 0).2
  have hrs : r ∈ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) :=
    (canonicalPeriodicEndpoints_mem_spectrum (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0).2
  have hd := (canonicalDiscriminant_sq_eq_four_iff (periodOnePotential (hillMiuraDiagonal u.val))
    (periodOnePotential_mem _) r).mpr hrs
  have he : r^2-(c:ℂ) ∈ singularHillSpectrum (periodOneOriginal q) := by
    apply (singularHillSpectrum_periodOne_iff_discriminant q _).mpr
    rw [hillHminusDiscriminant_shifted_miura_square q u.val (c:ℂ) r himage]
    exact hd
  obtain ⟨f,hf,hfe⟩ := (mem_singularHillSpectrum_iff (periodOneOriginal q) _).mp he
  have hb := singularHill_eigenvalue_re_lower_bound_of_norm_le B (periodOneOriginal q)
    ((norm_periodOneOriginal_le q).trans hq) (r^2-(c:ℂ)) f hf hfe
  have hn : 0 ≤ r.re := (hillMiura_gap_zero_contains_zero u).2
  simp only [sub_re,pow_two,mul_re,hr,ofReal_re,zero_mul,sub_zero] at hb
  change 1 ≤ r.re
  nlinarith

theorem shift_outside_of_zero_not_mem_hillMiura_spectrum
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c))
    (hz : (0:ℂ) ∉ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u))) :
    -c ∉ singularHillSpectrum (periodOneOriginal q) := by
  intro hs
  have hd := (singularHillSpectrum_periodOne_iff_discriminant q (-c)).mp hs
  have ht := hillHminusDiscriminant_shifted_miura_square q u c 0 himage
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_sub] at ht
  rw [ht] at hd
  exact hz ((canonicalDiscriminant_sq_eq_four_iff (periodOnePotential (hillMiuraDiagonal u))
    (periodOnePotential_mem _) 0).mp hd)

end NLS.KdV
