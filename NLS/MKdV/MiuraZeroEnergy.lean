import NLS.MKdV.MiuraNLSPositiveEndpoints
import NLS.ZakharovShabat.ClassicalDiagonalZeroEnergy
import NLS.FunctionalAnalysis.UnitIntervalMean

/-! # Exact Miura zero-energy trace and the original Fourier mean

The trace is computed from the actual continuous-profile IVP, including
all complex H¹ profiles. On the real slice zero energy is a periodic
endpoint exactly when the literal mean vanishes.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem unitIntervalMean_periodOneMiuraCurve (a : ScalarDomain 2) :
    unitIntervalMean (periodOneMiuraCurve a) = a.val 0 := by
  rw [unitIntervalMean_apply]
  calc
    _ = ∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
      exact (extend_coe (periodOneMiuraCurve a) ⟨x,hx'⟩).trans (periodOneMiuraCurve_apply a ⟨x,hx'⟩)
    _ = a.val 0 := by
      have h := periodOneCoefficient_periodOneSobolevSynthesis a 0
      simpa [periodOneCoefficient,fourierCoeffOn_one,halfCoefficient] using h

theorem quasiHillDiscriminant_miura_zero (a : ScalarDomain 2) :
    quasiHillDiscriminant (periodOneMiuraCurve a) 0 = 2*cosh (a.val 0) := by
  have h := quasiHillDiscriminant_eq_ZS (periodOneMiuraCurve a)
    (miuraDiagonalCurveCLM (periodOneMiuraCurve a)) (by intro t; rfl) 0
  simp only [zero_pow (by decide : 2 ≠ 0)] at h
  rw [h,classicalDiscriminant_diagonal_zero (periodOneMiuraCurve a) _ (by intro t; rfl),
    unitIntervalMean_periodOneMiuraCurve]

theorem canonicalDiscriminant_miura_zero (a : ScalarDomain 2) :
    canonicalDiscriminant (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) 0 =
      2*cosh (a.val 0) := by
  have h := canonicalDiscriminant_miuraDiagonalSource (periodOneMiuraCurve a) 0
  simpa only [miuraDiagonalSource_periodOneMiuraCurve,zero_pow (by decide : 2 ≠ 0),
    quasiHillDiscriminant_miura_zero] using h

theorem hillL2Discriminant_miura_zero (a : ScalarDomain 2) :
    hillL2Discriminant (sobolevMiuraHillPotential a) 0 = 2*cosh (a.val 0) :=
  (hillL2Discriminant_miura a 0).trans (quasiHillDiscriminant_miura_zero a)

theorem miura_mean_real (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) :
    (a.val 0).im = 0 := by
  have h := ha 0
  simp only [neg_zero] at h
  exact conj_eq_iff_im.mp h.symm

theorem miura_zero_trace_eq_two_iff_mean_zero (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    canonicalDiscriminant (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) 0 = 2 ↔
      a.val 0 = 0 := by
  rw [canonicalDiscriminant_miura_zero]
  have hmean : ((a.val 0).re : ℂ) = a.val 0 := by
    apply Complex.ext <;> simp only [ofReal_re,ofReal_im,miura_mean_real a ha]
  rw [← hmean,← ofReal_cosh]
  constructor
  · intro he
    have hc : Real.cosh (a.val 0).re = 1 := by
      have h := congrArg Complex.re he
      norm_num at h
      linarith
    have hz : (a.val 0).re = 0 := by
      by_contra hn
      have hgt := Real.one_lt_cosh.mpr hn
      linarith
    simp only [hz,ofReal_zero]
  · intro he
    have hz : (a.val 0).re = 0 := by exact_mod_cast he
    simp [hz]

theorem miura_ground_collapsed_iff_zero_trace (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    miuraNLSLeft a 0 = miuraNLSRight a 0 ↔
      canonicalDiscriminant (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) 0 = 2 := by
  have href := (miuraNLSEndpoints_reflection a 0).1
  simp only [neg_zero] at href
  constructor
  · intro he
    have hR : miuraNLSRight a 0 = 0 := by
      rw [he] at href
      linear_combination (1/2 : ℂ)*href
    have hlevel : canonicalDiscriminant (by simp)
        (periodOnePotential (sobolevSourceInclusion (a,a))) (miuraNLSRight a 0) = 2 := by
      simpa only [miuraNLSRight,realDiagonalH1Source,Int.zero_emod,ite_true] using
        (canonicalPeriodicEndpoints_discriminant_of_realType (by simp) (by norm_num) _
          (periodOnePotential_mem _) (isRealType_periodOnePotential (realDiagonalH1Source a ha).val
            (realDiagonalH1Source a ha).property) 0).2
    rwa [hR] at hlevel
  · intro he
    have hs : (0 : ℂ) ∈ periodicSpectrum (by simp)
        (periodOnePotential (sobolevSourceInclusion (a,a))) :=
      (canonicalDiscriminant_sq_eq_four_iff _ (periodOnePotential_mem _) 0).mp (by rw [he]; norm_num)
    obtain ⟨n,hx⟩ := (canonicalPeriodicEndpoints_exhaustive (by simp) (by norm_num) _
      (periodOnePotential_mem _) 0).mp hs
    change miuraNLSLeft a n = 0 ∨ miuraNLSRight a n = 0 at hx
    have hn : n = 0 := by
      have hxre : (miuraNLSLeft a n).re = 0 ∨ (miuraNLSRight a n).re = 0 := by
        rcases hx with hx | hx
        · exact Or.inl (congrArg Complex.re hx)
        · exact Or.inr (congrArg Complex.re hx)
      have hw := miuraNLSEndpoints_within a n
      rcases lt_trichotomy n 0 with hn | hn | hn
      · have hneg := miuraNLSRight_neg a ha hn
        rcases hxre with hxre | hxre <;> linarith
      · exact hn
      · have hpos := miuraNLSLeft_pos a ha hn
        rcases hxre with hxre | hxre <;> linarith
    subst n
    rcases hx with hx | hx
    · have hR : miuraNLSRight a 0 = 0 := by rw [hx] at href; linear_combination href
      exact hx.trans hR.symm
    · exact (href.trans (by rw [hx,neg_zero])).trans hx.symm

theorem miura_ground_collapsed_iff_mean_zero (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    miuraNLSLeft a 0 = miuraNLSRight a 0 ↔ a.val 0 = 0 :=
  (miura_ground_collapsed_iff_zero_trace a ha).trans (miura_zero_trace_eq_two_iff_mean_zero a ha)

end NLS.MKdV
