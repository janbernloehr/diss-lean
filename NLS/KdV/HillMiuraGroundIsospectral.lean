import NLS.KdV.HillMiuraGroundEnergy
import NLS.ZakharovShabat.SourceIsospectralSet

/-! # Isospectrality of arbitrary normalized ground Miura factors

The entire rough Hill discriminant determines the energy of every real
mean-zero Miura factor. The exact shifted-square trace identity then gives
the entire diagonal Dirac discriminant, including its normalization.
The two factors need not belong to a common local Miura chart.
-/
noncomputable section
set_option autoImplicit false
open NLS.ZakharovShabat
namespace NLS.KdV

/-- Equal entire rough Hill discriminants force equal normalized factor energies. -/
theorem miura_ground_energy_eq_of_discriminant_eq
    (q r : PeriodOneHminusOne) (u v : PeriodOneRealL2) (e f : ℝ)
    (hu : u.val 0 = 0) (hv : v.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hj : periodOneMiura v.val = r+periodOneL2Inclusion (lp.single 2 0 (f : ℂ)))
    (hΔ : hillHminusDiscriminant q = hillHminusDiscriminant r) : e = f := by
  have hq : hillHminusRadicand q (-(f : ℂ)) = 0 := by
    rw [hillHminusRadicand,hΔ,hillHminusDiscriminant_neg_energy_eq_two r v f hv hj]
    norm_num
  have hr : hillHminusRadicand r (-(e : ℂ)) = 0 := by
    rw [hillHminusRadicand,←hΔ,hillHminusDiscriminant_neg_energy_eq_two q u e hu hi]
    norm_num
  have h₁ := neg_miura_energy_le_re_of_hillHminusRadicand_eq_zero q u e hi _ hq
  have h₂ := neg_miura_energy_le_re_of_hillHminusRadicand_eq_zero r v f hj _ hr
  simp only [Complex.neg_re,Complex.ofReal_re] at h₁ h₂
  linarith

/-- The actual normalized diagonal Dirac discriminants agree at every frequency. -/
theorem miura_ground_discriminant_eq_of_hill_discriminant_eq
    (q r : PeriodOneHminusOne) (u v : PeriodOneRealL2) (e f : ℝ)
    (hu : u.val 0 = 0) (hv : v.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hj : periodOneMiura v.val = r+periodOneL2Inclusion (lp.single 2 0 (f : ℂ)))
    (hΔ : hillHminusDiscriminant q = hillHminusDiscriminant r) :
    canonicalDiscriminant (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) =
      canonicalDiscriminant (by simp) (periodOnePotential (hillMiuraDiagonal v.val)) := by
  have he := miura_ground_energy_eq_of_discriminant_eq q r u v e f hu hv hi hj hΔ
  subst f
  funext z
  rw [←hillHminusDiscriminant_shifted_miura_square q u.val (e : ℂ) z hi,
    ←hillHminusDiscriminant_shifted_miura_square r v.val (e : ℂ) z hj,hΔ]

/-- Arbitrary normalized real ground factors have the same original periodic
Dirac spectrum with all algebraic multiplicities. -/
theorem miura_ground_mem_isospectralSet_of_hill_discriminant_eq
    (q r : PeriodOneHminusOne) (u v : PeriodOneRealL2) (e f : ℝ)
    (hu : u.val 0 = 0) (hv : v.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hj : periodOneMiura v.val = r+periodOneL2Inclusion (lp.single 2 0 (f : ℂ)))
    (hΔ : hillHminusDiscriminant q = hillHminusDiscriminant r) :
    hillMiuraRealSource v ∈ sourceIsospectralSet (by simp) (hillMiuraRealSource u) := by
  apply (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num) _ _).mpr
  exact (miura_ground_discriminant_eq_of_hill_discriminant_eq
    q r u v e f hu hv hi hj hΔ).symm

end NLS.KdV
