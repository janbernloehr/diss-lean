import NLS.KdV.HillMiuraCriticalFrequencies
import NLS.KdV.HillMiuraSquaredEnumeration
import NLS.KdV.HillMiuraGroundEnergy
import NLS.KdV.HillHminusOneTraceParity

/-! # Full squared enumeration at the critical Miura energy

The square map is unramified away from zero. At zero the original Hill
root is simple and the one-sided Dirac enumeration has one occurrence.
Thus the critical factor retains every actual characteristic multiplicity.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.ZakharovShabat NLS.ComplexAnalysis

theorem hillMiuraSquaredLabels_critical_roots_iff
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (e : ℝ)
    (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (E : ℂ) :
    hillHminusRadicand q E = 0 ↔ ∃ j : ℕ, E = (hillMiuraSquaredLabels u.val e j : ℂ) := by
  have hcrit (z : ℂ) := canonicalDiscriminant_sq_eq_four_iff_finite
    (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) z
  constructor
  · intro hE
    let z := Complex.sqrt (E+(e : ℂ))
    have hs : z^2 = E+(e : ℂ) := complex_sqrt_sq _
    have ht := hillHminusDiscriminant_shifted_miura_square q u.val (e : ℂ) z hi
    rw [hs,add_sub_cancel_right] at ht
    have hD : z ∈ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) := by
      apply (hcrit z).mp
      rw [←ht]
      exact sub_eq_zero.mp hE
    have him := periodicSpectrum_im_eq_zero_of_realType (by simp)
      (periodOnePotential (hillMiuraDiagonal u.val))
      (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) z hD
    have hzC : (z.re : ℂ) = z := Complex.ext rfl him.symm
    obtain ⟨j,hj⟩ : ∃ j : ℕ, hillMiuraPositiveFrequencies u.val j = z.re := by
      rcases (re_sqrt_nonneg (E+(e : ℂ))).eq_or_lt with hz | hz
      · exact ⟨0,(hillMiuraPositiveFrequencies_zero_of_meanZero u hm).trans hz⟩
      · exact (hillMiuraPositiveFrequencies_exhaustive u z.re hz).mp (hzC.symm ▸ hD)
    refine ⟨j,?_⟩
    calc
      E = z^2-(e : ℂ) := by rw [hs,add_sub_cancel_right]
      _ = (hillMiuraSquaredLabels u.val e j : ℂ) := by
        rw [←hzC,←hj]
        simp only [hillMiuraSquaredLabels,ofReal_sub,ofReal_pow]
  · rintro ⟨j,rfl⟩
    have ht := hillHminusDiscriminant_shifted_miura_square q u.val (e : ℂ)
      (hillMiuraPositiveFrequencies u.val j : ℂ) hi
    change hillHminusDiscriminant q (hillMiuraSquaredLabels u.val e j)^2-4 = 0
    rw [show (hillMiuraSquaredLabels u.val e j : ℂ) =
      (hillMiuraPositiveFrequencies u.val j : ℂ)^2-(e : ℂ) by
        simp only [hillMiuraSquaredLabels,ofReal_sub,ofReal_pow],ht]
    exact sub_eq_zero.mpr ((hcrit _).mpr (hillMiuraPositiveFrequencies_mem_spectrum u j))

theorem hillMiuraSquaredLabels_critical_multiplicity
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ))) (x : ℝ) :
    (∑ᶠ j : ℕ, if hillMiuraSquaredLabels u.val e j = x then (1 : ℕ) else 0) =
      analyticOrderNatAt (hillHminusRadicand q) (x : ℂ) := by
  by_cases hx : ∃ j : ℕ, hillMiuraSquaredLabels u.val e j = x
  · obtain ⟨j,hj⟩ := hx
    let z := hillMiuraPositiveFrequencies u.val j
    have hif (i : ℕ) : hillMiuraSquaredLabels u.val e i = x ↔ hillMiuraPositiveFrequencies u.val i = z := by
      have hi0 := hillMiuraPositiveFrequencies_nonneg u i
      have hj0 := hillMiuraPositiveFrequencies_nonneg u j
      change z^2-e = x at hj
      change hillMiuraPositiveFrequencies u.val i^2-e = x ↔ _
      constructor <;> intro h <;> nlinarith
    have hfun : (fun i : ℕ => if hillMiuraSquaredLabels u.val e i = x then (1 : ℕ) else 0) =
        (fun i => if hillMiuraPositiveFrequencies u.val i = z then 1 else 0) := by
      funext i
      simp only [hif i]
    rw [hfun]
    by_cases hj0 : j = 0
    · subst j
      have hz : z = 0 := hillMiuraPositiveFrequencies_zero_of_meanZero u hm
      have hx : x = -e := by
        change z^2-e = x at hj
        rw [hz,zero_pow (by norm_num),zero_sub] at hj
        exact hj.symm
      rw [hz,hillMiuraPositiveFrequencies_zero_count u hm,hx,
        neg_miura_energy_eq_hillHminusLowestRealRoot q hr u e hm hi]
      exact (hillHminusLowestRealRoot_order_one q hr).symm
    · have hzpos : 0 < z := hillMiuraPositiveFrequencies_pos_of_pos u j (by omega)
      rw [hillMiuraPositiveFrequencies_multiplicity u z hzpos]
      have hxC : (x : ℂ) = (z : ℂ)^2-(e : ℂ) := by
        rw [←hj]
        simp only [hillMiuraSquaredLabels,z,ofReal_sub,ofReal_pow]
      rw [hxC,analyticOrderNatAt_hillHminusRadicand_shifted_miura q u.val (e : ℂ) (z : ℂ)
        (by exact_mod_cast hzpos.ne') hi]
  · have hn : ∀ j : ℕ, hillMiuraSquaredLabels u.val e j ≠ x := fun j h => hx ⟨j,h⟩
    simp only [if_neg (hn _),finsum_zero]
    symm
    by_contra hne
    have hroot := apply_eq_zero_of_analyticOrderNatAt_ne_zero hne
    obtain ⟨j,hj⟩ := (hillMiuraSquaredLabels_critical_roots_iff q u e hm hi (x : ℂ)).mp hroot
    exact hx ⟨j,(Complex.ofReal_injective hj).symm⟩

end NLS.KdV
