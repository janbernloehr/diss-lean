import NLS.KdV.HillMiuraSquaredEnumeration
import NLS.KdV.HillMiuraGroundEnergy
import NLS.KdV.HillHminusOneTraceParity

/-! # Squared Miura enumeration at the actual critical ground factor

Zero frequency is present and its two Dirac occurrences give the single
simple lowest Hill energy after squaring. Positive frequencies retain
their full actual algebraic multiplicity. No exterior-energy premise is
used, and no inverse at the critical Miura factor is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

/-- Every slot after the initial one has strictly positive frequency,
including when the central gap is collapsed at zero. -/
theorem hillMiuraPositiveFrequencies_pos_of_ne_zero
    (u : PeriodOneRealL2) (j : ℕ) (hj : j ≠ 0) :
    0 < hillMiuraPositiveFrequencies u.val j := by
  obtain ⟨n,hn,hslot⟩ := singletonPairedEnumeration_slot j hj
  have hp := hillMiura_positive_gap_left_pos u (n : ℤ) (by exact_mod_cast hn)
  change 0 < (hillMiuraDiracLeft u.val n).re at hp
  rcases hslot with rfl | rfl
  · rw [hillMiuraPositiveFrequencies_left u.val n hn]
    exact hp
  · rw [hillMiuraPositiveFrequencies_right u.val n hn]
    exact hp.trans_le (hillMiuraDiracPair_ordered u.val n)

theorem hillMiuraPositiveFrequencies_initial_of_meanZero
    (u : PeriodOneRealL2) (hm : u.val 0 = 0) : hillMiuraPositiveFrequencies u.val 0 = 0 := by
  have hr := (hillMiura_central_endpoints_eq_zero u hm).2
  change hillMiuraDiracRight u.val 0 = 0 at hr
  rw [hillMiuraPositiveFrequencies_initial,hr,zero_re]

theorem hillMiuraSquaredLabels_initial_of_meanZero
    (u : PeriodOneRealL2) (hm : u.val 0 = 0) (c : ℝ) : hillMiuraSquaredLabels u.val c 0 = -c := by
  simp only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_initial_of_meanZero u hm,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_sub]

theorem hillMiuraSquaredLabels_roots_iff_of_meanZero
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hm : u.val 0 = 0) (E : ℂ) :
    hillHminusRadicand q E = 0 ↔ ∃ j : ℕ, E = (hillMiuraSquaredLabels u.val c j : ℂ) := by
  have hcrit (z : ℂ) := canonicalDiscriminant_sq_eq_four_iff_finite
    (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) z
  constructor
  · intro hE
    let z := Complex.sqrt (E+(c : ℂ))
    have hsq : z^2 = E+(c : ℂ) := NLS.ComplexAnalysis.complex_sqrt_sq _
    have henergy : z^2-(c : ℂ) = E := by rw [hsq,add_sub_cancel_right]
    have htrace := hillHminusDiscriminant_shifted_miura_square q u.val (c : ℂ) z himage
    rw [henergy] at htrace
    have hD : z ∈ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) := by
      apply (hcrit z).mp
      rw [← htrace]
      exact sub_eq_zero.mp hE
    have him : z.im = 0 := periodicSpectrum_im_eq_zero_of_realType (by simp)
      (periodOnePotential (hillMiuraDiagonal u.val))
      (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) z hD
    have hzC : (z.re : ℂ) = z := Complex.ext rfl him.symm
    by_cases hz0 : z = 0
    · refine ⟨0,?_⟩
      rw [hillMiuraSquaredLabels_initial_of_meanZero u hm]
      simpa only [hz0,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_sub,ofReal_neg] using henergy.symm
    have hzpos : 0 < z.re := by
      apply lt_of_le_of_ne (re_sqrt_nonneg _)
      intro he
      have hz : z = 0 := Complex.ext he.symm him
      exact hz0 hz
    obtain ⟨j,hj⟩ := (hillMiuraPositiveFrequencies_exhaustive u z.re hzpos).mp (hzC.symm ▸ hD)
    refine ⟨j,?_⟩
    calc
      E = z^2-(c : ℂ) := henergy.symm
      _ = (hillMiuraSquaredLabels u.val c j : ℂ) := by
        rw [← hzC,← hj]
        simp only [hillMiuraSquaredLabels,ofReal_sub,ofReal_pow]
  · rintro ⟨j,rfl⟩
    have hs := hillMiuraPositiveFrequencies_mem_spectrum u j
    have htrace := hillHminusDiscriminant_shifted_miura_square q u.val (c : ℂ)
      (hillMiuraPositiveFrequencies u.val j : ℂ) himage
    change hillHminusDiscriminant q (hillMiuraSquaredLabels u.val c j)^2-4 = 0
    rw [show (hillMiuraSquaredLabels u.val c j : ℂ) =
      (hillMiuraPositiveFrequencies u.val j : ℂ)^2-(c : ℂ) by
        simp only [hillMiuraSquaredLabels,ofReal_sub,ofReal_pow],htrace]
    exact sub_eq_zero.mpr ((hcrit _).mpr hs)

theorem hillMiuraSquaredLabels_global_multiplicity_of_meanZero
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hm : u.val 0 = 0) (x : ℝ) :
    (∑ᶠ j : ℕ, if hillMiuraSquaredLabels u.val c j = x then (1 : ℕ) else 0) =
      analyticOrderNatAt (hillHminusRadicand q) (x : ℂ) := by
  by_cases hx0 : x = -c
  · subst x
    have he := neg_miura_energy_eq_hillHminusLowestRealRoot q hq u c hm himage
    have ho : analyticOrderNatAt (hillHminusRadicand q) ((-c : ℝ) : ℂ) = 1 := by
      rw [he]
      exact hillHminusLowestRealRoot_order_one q hq
    rw [ho,finsum_eq_single _ 0]
    · simp only [hillMiuraSquaredLabels_initial_of_meanZero u hm,ite_true]
    · intro j hj
      apply if_neg
      have hp := hillMiuraPositiveFrequencies_pos_of_ne_zero u j hj
      change hillMiuraPositiveFrequencies u.val j^2-c ≠ -c
      nlinarith
  by_cases hx : ∃ j : ℕ, hillMiuraSquaredLabels u.val c j = x
  · obtain ⟨j,hj⟩ := hx
    let z : ℝ := hillMiuraPositiveFrequencies u.val j
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [hillMiuraSquaredLabels_initial_of_meanZero u hm] at hj
      exact hx0 hj.symm
    have hzpos : 0 < z := hillMiuraPositiveFrequencies_pos_of_ne_zero u j hj0
    have hif (i : ℕ) : hillMiuraSquaredLabels u.val c i = x ↔ hillMiuraPositiveFrequencies u.val i = z := by
      have hi := hillMiuraPositiveFrequencies_nonneg u i
      change z^2-c = x at hj
      change hillMiuraPositiveFrequencies u.val i^2-c = x ↔ _
      constructor <;> intro h <;> nlinarith
    have hfun : (fun i : ℕ => if hillMiuraSquaredLabels u.val c i = x then (1 : ℕ) else 0) =
        (fun i => if hillMiuraPositiveFrequencies u.val i = z then 1 else 0) := by
      funext i
      simp only [hif i]
    rw [hfun,hillMiuraPositiveFrequencies_multiplicity u z hzpos]
    have hxC : (x : ℂ) = (z : ℂ)^2-(c : ℂ) := by
      rw [← hj]
      simp only [hillMiuraSquaredLabels,z,ofReal_sub,ofReal_pow]
    rw [hxC,analyticOrderNatAt_hillHminusRadicand_shifted_miura q u.val (c : ℂ) (z : ℂ)
      (by exact_mod_cast hzpos.ne') himage]
  · have hn : ∀ j : ℕ, hillMiuraSquaredLabels u.val c j ≠ x := fun j h => hx ⟨j,h⟩
    simp only [if_neg (hn _),finsum_zero]
    symm
    by_contra hne
    have hr := apply_eq_zero_of_analyticOrderNatAt_ne_zero hne
    obtain ⟨j,hj⟩ := (hillMiuraSquaredLabels_roots_iff_of_meanZero q u c himage hm (x : ℂ)).mp hr
    exact hx ⟨j,(Complex.ofReal_injective hj).symm⟩

end NLS.KdV
