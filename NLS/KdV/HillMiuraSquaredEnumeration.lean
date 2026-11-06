import NLS.KdV.HminusOneMiuraIsospectral
import NLS.KdV.HillMiuraPositiveEnumeration
import NLS.ComplexAnalysis.ShiftedSquareRootBounds

/-! # Complete squared Miura enumeration at an outside-spectrum shift

An energy translation below the full Hill spectrum excludes zero Dirac
frequency. Squaring the positive enumeration therefore preserves every
algebraic occurrence, including the single bottom endpoint and repeated
positive pairs. All roots of the actual Hill characteristic are covered.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.ZakharovShabat

def hillMiuraSquaredLabels (u : Coeff 2) (c : ℝ) (j : ℕ) : ℝ :=
  hillMiuraPositiveFrequencies u j^2-c

theorem monotone_hillMiuraSquaredLabels (u : PeriodOneRealL2) (c : ℝ) :
    Monotone (hillMiuraSquaredLabels u.val c) := by
  intro i j hij
  have h := monotone_hillMiuraPositiveFrequencies u hij
  have hi := hillMiuraPositiveFrequencies_nonneg u i
  have hj := hillMiuraPositiveFrequencies_nonneg u j
  dsimp only [hillMiuraSquaredLabels]
  nlinarith

theorem hillMiuraSquaredLabels_finite_fiber (u : PeriodOneRealL2) (c x : ℝ) :
    {j : ℕ | hillMiuraSquaredLabels u.val c j = x}.Finite := by
  by_cases hx : ∃ j : ℕ, hillMiuraSquaredLabels u.val c j = x
  · obtain ⟨j,hj⟩ := hx
    apply (hillMiuraPositiveFrequencies_finite_fiber u (hillMiuraPositiveFrequencies u.val j)).subset
    intro i hi
    have hni := hillMiuraPositiveFrequencies_nonneg u i
    have hnj := hillMiuraPositiveFrequencies_nonneg u j
    change hillMiuraPositiveFrequencies u.val i = hillMiuraPositiveFrequencies u.val j
    change hillMiuraPositiveFrequencies u.val i^2-c = x at hi
    change hillMiuraPositiveFrequencies u.val j^2-c = x at hj
    nlinarith
  · have he : {j : ℕ | hillMiuraSquaredLabels u.val c j = x} = ∅ := by
      ext j
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      exact fun h => hx ⟨j,h⟩
    rw [he]
    exact finite_empty

theorem hillMiuraSquaredLabels_roots_iff_of_radicand_ne_zero
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ)) ≠ 0) (E : ℂ) :
    hillHminusRadicand q E = 0 ↔ ∃ j : ℕ, E = (hillMiuraSquaredLabels u.val c j : ℂ) := by
  have hzero := zero_not_mem_periodicSpectrum_of_shifted_miura_of_radicand_ne_zero q u.val (c : ℂ) himage hc
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
    have hzpos : 0 < z.re := by
      apply lt_of_le_of_ne (re_sqrt_nonneg _)
      intro he
      have hz : z = 0 := Complex.ext he.symm him
      exact hzero (hz ▸ hD)
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

theorem hillMiuraSquaredLabels_global_multiplicity_of_radicand_ne_zero
    (q : PeriodOneHminusOne) (_hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : hillHminusRadicand q (-(c : ℂ)) ≠ 0) (x : ℝ) :
    (∑ᶠ j : ℕ, if hillMiuraSquaredLabels u.val c j = x then (1 : ℕ) else 0) =
      analyticOrderNatAt (hillHminusRadicand q) (x : ℂ) := by
  have hzero := zero_not_mem_periodicSpectrum_of_shifted_miura_of_radicand_ne_zero q u.val (c : ℂ) himage hc
  by_cases hx : ∃ j : ℕ, hillMiuraSquaredLabels u.val c j = x
  · obtain ⟨j,hj⟩ := hx
    let z : ℝ := hillMiuraPositiveFrequencies u.val j
    have hzpos : 0 < z := hillMiuraPositiveFrequencies_pos_of_zero_not_mem u hzero j
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
    obtain ⟨j,hj⟩ := (hillMiuraSquaredLabels_roots_iff_of_radicand_ne_zero q u c himage hc (x : ℂ)).mp hr
    exact hx ⟨j,(Complex.ofReal_injective hj).symm⟩

/-- Compatibility with the original physical outside-spectrum hypothesis. -/
theorem hillMiuraSquaredLabels_roots_iff
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (E : ℂ) :
    hillHminusRadicand q E = 0 ↔ ∃ j : ℕ, E = (hillMiuraSquaredLabels u.val c j : ℂ) := by
  exact hillMiuraSquaredLabels_roots_iff_of_radicand_ne_zero q u c himage (hillHminusRadicand_ne_zero_of_not_mem_singularHillSpectrum q (-(c : ℂ)) hc) E

/-- Compatibility with the original physical outside-spectrum hypothesis. -/
theorem hillMiuraSquaredLabels_global_multiplicity
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (x : ℝ) :
    (∑ᶠ j : ℕ, if hillMiuraSquaredLabels u.val c j = x then (1 : ℕ) else 0) =
      analyticOrderNatAt (hillHminusRadicand q) (x : ℂ) := by
  exact hillMiuraSquaredLabels_global_multiplicity_of_radicand_ne_zero q hq u c himage (hillHminusRadicand_ne_zero_of_not_mem_singularHillSpectrum q (-(c : ℂ)) hc) x

end NLS.KdV
