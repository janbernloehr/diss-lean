import NLS.MKdV.MiuraPositiveMultiplicity
import NLS.MKdV.MiuraHillRealLabels
import NLS.SequenceSpaces.OrderedNaturalEnumerationUnique

/-! # The squared positive NLS sequence is the intrinsic Miura Hill labeling

Equal analytic multiplicities determine the ordered natural enumeration.
The single ground slot accounts for the exact ramification at zero.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.KdV
open scoped ENNReal ComplexConjugate Classical
namespace NLS.MKdV

def miuraSquaredNLS (a : ScalarDomain 2) (j : ℕ) : ℝ := (miuraPositiveFrequency a j)^2

theorem monotone_miuraSquaredNLS (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) : Monotone (miuraSquaredNLS a) := by
  intro i j hij
  exact (sq_le_sq₀ (miuraPositiveFrequency_nonnegative a ha i)
    (miuraPositiveFrequency_nonnegative a ha j)).mpr (monotone_miuraPositiveFrequency a ha hij)

theorem miuraSquaredNLS_finite_fiber (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (x : ℝ) :
    {j : ℕ | miuraSquaredNLS a j = x}.Finite := by
  by_cases hex : ∃ j, miuraSquaredNLS a j = x
  · obtain ⟨j,hj⟩ := hex
    apply (miuraPositiveFrequency_finite_fiber a ha (miuraPositiveFrequency a j)).subset
    intro k hk
    exact (sq_eq_sq₀ (miuraPositiveFrequency_nonnegative a ha k)
      (miuraPositiveFrequency_nonnegative a ha j)).mp (hk.trans hj.symm)
  · have he : {j : ℕ | miuraSquaredNLS a j = x} = ∅ := by
      ext j
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun hj => hex ⟨j,hj⟩
    rw [he]
    exact Set.finite_empty

theorem miuraSquaredNLS_multiplicity (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (x : ℝ) :
    (∑ᶠ j : ℕ, if miuraSquaredNLS a j = x then (1 : ℕ) else 0) =
      analyticOrderNatAt (hillL2Radicand (sobolevMiuraHillPotential a)) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hcount : (∑ᶠ j : ℕ, if miuraSquaredNLS a j = x then (1 : ℕ) else 0) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro j
      apply if_neg
      exact ne_of_gt (lt_of_lt_of_le hx (sq_nonneg (miuraPositiveFrequency a j)))
    have hne : hillL2Radicand (sobolevMiuraHillPotential a) (x : ℂ) ≠ 0 := by
      intro he
      have hn := (miuraHillRadicand_root_nonnegative a ha x he).2
      exact (not_le_of_gt hx) hn
    have hord := (analyticOnNhd_hillL2Radicand (sobolevMiuraHillPotential a) x
      (mem_univ _)).analyticOrderAt_eq_zero.mpr hne
    rw [hcount,analyticOrderNatAt,hord,ENat.toNat_zero]
  · have hcount : (∑ᶠ j : ℕ, if miuraSquaredNLS a j = 0 then (1 : ℕ) else 0) =
        ∑ᶠ j : ℕ, if miuraPositiveFrequency a j = 0 then (1 : ℕ) else 0 := by
      apply finsum_congr
      intro j
      simp only [miuraSquaredNLS,sq_eq_zero_iff]
    have h1 := miuraPositiveFrequency_zero_multiplicity a ha
    have h2 := miuraHillRadicand_zero_multiplicity a
    rw [hcount]
    simp only [ofReal_zero]
    omega
  · let r := Real.sqrt x
    have hr : 0 < r := Real.sqrt_pos.mpr hx
    have hrsq : r^2 = x := Real.sq_sqrt hx.le
    have hcount : (∑ᶠ j : ℕ, if miuraSquaredNLS a j = x then (1 : ℕ) else 0) =
        ∑ᶠ j : ℕ, if miuraPositiveFrequency a j = r then (1 : ℕ) else 0 := by
      apply finsum_congr
      intro j
      have he : miuraSquaredNLS a j = x ↔ miuraPositiveFrequency a j = r := by
        rw [miuraSquaredNLS,← hrsq]
        exact sq_eq_sq₀ (miuraPositiveFrequency_nonnegative a ha j) hr.le
      simp only [he]
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have he : (r : ℂ)^2 = (x : ℂ) := by exact_mod_cast hrsq
    rw [hcount,miuraPositiveFrequency_count_pos a ha r hr,
      ← analyticOrderNatAt_miuraHillRadicand_energy a r hrne,he]

theorem miuraHillLabels_eq_squaredNLS (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) : miuraHillLabels a ha = miuraSquaredNLS a :=
  ordered_natural_enumeration_unique _ _ (monotone_miuraHillLabels a ha)
    (monotone_miuraSquaredNLS a ha) (fun x => (miuraHillLabels_multiplicity a ha x).1)
    (miuraSquaredNLS_finite_fiber a ha) (fun x =>
      (miuraHillLabels_multiplicity a ha x).2.trans (miuraSquaredNLS_multiplicity a ha x).symm)

end NLS.MKdV
