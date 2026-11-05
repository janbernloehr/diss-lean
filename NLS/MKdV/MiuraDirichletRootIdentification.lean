import NLS.MKdV.MiuraRotatedDirichletCharacteristic
import NLS.MKdV.MiuraGapIdentification
import NLS.MKdV.MiuraHillDirichletPositivity
import NLS.ZakharovShabat.AuxiliaryPeriodOneBoundaryInterlacing
import NLS.ZakharovShabat.SourceBoundaryRootDifferential

/-! # Exact indexed identification of the original Dirichlet divisor

The independently labeled scalar energies are the squares of the positive
rotated source roots. Negative roots have the opposite sign, and the central
root is exactly zero. Closed periodic gaps are included throughout.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraRotatedDirichletRoots (a : ScalarDomain 2) : ℤ → ℂ :=
  canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
    (sourcePhase (sobolevSourceInclusion (a,a)))

theorem miuraRotatedDirichletRoots_real (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℤ) :
    (miuraRotatedDirichletRoots a n).im = 0 :=
  canonicalPeriodOneBoundaryRoots_im_eq_zero (by simp) (by norm_num) .dirichlet _
    (isRealType_sourcePhase _ (realDiagonalH1Source a ha).property) n

theorem miuraRotatedDirichletRoots_mem_gap (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℤ) :
    (miuraRotatedDirichletRoots a n).re ∈
      Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re := by
  have h := canonicalAuxiliaryPeriodOneRoots_mem_gap (by simp) (by norm_num) .dirichlet
    (sobolevSourceInclusion (a,a)) (realDiagonalH1Source a ha).property n
  rw [canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase] at h
  exact h

theorem miuraRotatedDirichletRoots_pos (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) {n : ℤ} (hn : 0 < n) :
    0 < (miuraRotatedDirichletRoots a n).re :=
  (miuraNLSLeft_pos a ha hn).trans_le (miuraRotatedDirichletRoots_mem_gap a ha n).1

theorem miuraRotatedDirichletRoots_neg (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) {n : ℤ} (hn : n < 0) :
    (miuraRotatedDirichletRoots a n).re < 0 :=
  (miuraRotatedDirichletRoots_mem_gap a ha n).2.trans_lt (miuraNLSRight_neg a ha hn)

theorem miuraDirichletEnergy_eq_frequency_sq (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hi : z.im = 0) (hz : z.re ∈ Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re)
    (hzero : periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (sourcePhase (sobolevSourceInclusion (a,a))) z = 0) :
    (hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1
      (realSobolevMiuraHillPotential a ha).property.2 n hn : ℂ) = z^2 := by
  have hp : 0 < z.re := (miuraNLSLeft_pos a ha (show (0 : ℤ) < n by omega)).trans_le hz.1
  have hne : z ≠ 0 := by intro h;simp [h] at hp
  have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
  have hgap : z.re^2 ∈ Icc (miuraHillLabels a ha (2*n-1)) (miuraHillLabels a ha (2*n)) := by
    rw [← miuraHillGap_square_image a ha n hn]
    exact ⟨z.re,hz,rfl⟩
  have hscalar := (miura_rotated_Dirichlet_zero_iff a z hne).mp hzero
  have hs : ((z.re^2 : ℝ) : ℂ) = z^2 := by rw [ofReal_pow,he]
  rw [← hs,← realSobolevMiuraHillPotential_toCoeff a ha] at hscalar
  have h := hillDirichletEnergy_eq_of_zero_in_gap (realSobolevMiuraHillPotential a ha).val
    (realSobolevMiuraHillPotential a ha).property.1
    (realSobolevMiuraHillPotential a ha).property.2 n hn (z.re^2) hgap hscalar
  exact (congrArg (fun x : ℝ => (x : ℂ)) h).trans hs

theorem miuraRotatedDirichletRoots_sq (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    (miuraRotatedDirichletRoots a n)^2 =
      (hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
        (realSobolevMiuraHillPotential a ha).property.1
        (realSobolevMiuraHillPotential a ha).property.2 n hn : ℂ) := by
  exact (miuraDirichletEnergy_eq_frequency_sq a ha n hn _
    (miuraRotatedDirichletRoots_real a ha n) (miuraRotatedDirichletRoots_mem_gap a ha n)
    (periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero (by simp) (by norm_num) .dirichlet _ n)).symm

theorem miuraRotatedDirichletRoots_neg_nat (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    miuraRotatedDirichletRoots a (-(n : ℤ)) = -miuraRotatedDirichletRoots a n := by
  let z := miuraRotatedDirichletRoots a (-(n : ℤ))
  have hi : (-z).im = 0 := by simp only [neg_im,miuraRotatedDirichletRoots_real a ha,neg_zero,z]
  have hgap : (-z).re ∈ Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re := by
    have h := miuraRotatedDirichletRoots_mem_gap a ha (-(n : ℤ))
    rw [(miuraNLSEndpoints_reflection a (-(n : ℤ))).1,
      (miuraNLSEndpoints_reflection a (-(n : ℤ))).2,neg_neg] at h
    simp only [neg_re] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have hzero : periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (sourcePhase (sobolevSourceInclusion (a,a))) (-z) = 0 := by
    rw [miura_rotated_Dirichlet_characteristic_odd]
    change -periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (sourcePhase (sobolevSourceInclusion (a,a)))
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
        (sourcePhase (sobolevSourceInclusion (a,a))) (-(n : ℤ))) = 0
    rw [periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero,neg_zero]
  have hs := miuraDirichletEnergy_eq_frequency_sq a ha n hn (-z) hi hgap hzero
  rw [neg_sq,← miuraRotatedDirichletRoots_sq a ha n hn] at hs
  have hzn := miuraRotatedDirichletRoots_neg a ha (show -(n : ℤ) < 0 by omega)
  have hzp := miuraRotatedDirichletRoots_pos a ha (show (0 : ℤ) < n by omega)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
  · have hr := congrArg Complex.re h
    change (miuraRotatedDirichletRoots a n).re = (miuraRotatedDirichletRoots a (-(n : ℤ))).re at hr
    linarith
  · change miuraRotatedDirichletRoots a n = -z at h
    simpa only [neg_neg] using (congrArg Neg.neg h).symm

theorem miuraRotatedDirichletRoots_zero (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) : miuraRotatedDirichletRoots a 0 = 0 := by
  obtain ⟨n,hn⟩ := (canonicalPeriodOneBoundaryRoots_exhaustive (by simp) (by norm_num) .dirichlet
    (sourcePhase (sobolevSourceInclusion (a,a))) 0).mp
      ((periodOneBoundaryCharacteristic_eq_zero_iff (by simp) (by norm_num) .dirichlet _ 0).mp
        (miura_rotated_Dirichlet_characteristic_zero a))
  change miuraRotatedDirichletRoots a n = 0 at hn
  have he : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · have hp := miuraRotatedDirichletRoots_neg a ha h
      simp only [hn,zero_re] at hp
      exact (lt_irrefl 0 hp).elim
    · exact h
    · have hp := miuraRotatedDirichletRoots_pos a ha h
      simp only [hn,zero_re] at hp
      exact (lt_irrefl 0 hp).elim
  simpa only [he] using hn

end NLS.MKdV
