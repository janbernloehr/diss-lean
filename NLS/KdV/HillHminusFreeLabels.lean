import NLS.KdV.HillHminusOneCanonicalRealLabels
import NLS.KdV.HillFreeSpectrum
import NLS.SequenceSpaces.SingletonPairedEnumeration

/-! The ENTIRE intrinsic free Hill energy enumeration, including the
single bottom value and EVERY repeated positive pair. Full analytic
multiplicities determine the labels; asymptotic agreement is not used. -/
noncomputable section
open Set Complex
open scoped Classical
namespace NLS.KdV

theorem hillHminusRadicand_zero_eq_free : hillHminusRadicand 0 = hillL2Radicand 0 := by
  funext z
  simpa only [map_zero] using hillHminusRadicand_eq_hillL2 (0 : Coeff 2) z

def hillHminusFreeLabels : ℕ → ℝ :=
  singletonPairedEnumeration (freeHillValue 0) (fun n => freeHillValue n) (fun n => freeHillValue n)

theorem monotone_hillHminusFreeLabels : Monotone hillHminusFreeLabels :=
  monotone_singletonPairedEnumeration _ _ _
    (fun _ hn => strictMono_freeHillValue hn) (fun _ _ => le_rfl)
    (fun _ _ _ hij => strictMono_freeHillValue hij)

theorem hillHminusFreeLabels_finite_fiber (x : ℝ) : {j : ℕ | hillHminusFreeLabels j = x}.Finite :=
  singletonPairedEnumeration_finite_fiber _ _ _
    (fun _ hn => strictMono_freeHillValue hn) (fun _ _ => le_rfl)
    (fun _ _ _ hij => strictMono_freeHillValue hij) x

theorem hillHminusFreeLabels_roots_iff (z : ℂ) :
    hillHminusRadicand 0 z = 0 ↔ ∃ j : ℕ, z = (hillHminusFreeLabels j:ℂ) := by
  rw [hillHminusRadicand_zero_eq_free,hillL2Radicand_free_zero_iff]
  constructor
  · rintro ⟨n,rfl⟩
    by_cases hn : n = 0
    · subst n
      exact ⟨0,rfl⟩
    · refine ⟨2*n,?_⟩
      rw [hillHminusFreeLabels,singletonPairedEnumeration_right _ _ _ n (by omega)]
  · rintro ⟨j,rfl⟩
    by_cases hj : j = 0
    · subst j
      exact ⟨0,rfl⟩
    · obtain ⟨n,hn,hj⟩ := singletonPairedEnumeration_slot j hj
      rcases hj with rfl | rfl
      · exact ⟨n,by rw [hillHminusFreeLabels,singletonPairedEnumeration_left _ _ _ n hn]⟩
      · exact ⟨n,by rw [hillHminusFreeLabels,singletonPairedEnumeration_right _ _ _ n hn]⟩

theorem hillHminusFreeLabels_global_multiplicity (x : ℝ) :
    (∑ᶠ j : ℕ, if hillHminusFreeLabels j = x then (1:ℕ) else 0) =
      analyticOrderNatAt (hillHminusRadicand 0) (x:ℂ) := by
  have hstart : ∀ n : ℕ, 0 < n → freeHillValue 0 < freeHillValue n :=
    fun _ hn => strictMono_freeHillValue hn
  have hpair : ∀ n : ℕ, 0 < n → freeHillValue n ≤ freeHillValue n := fun _ _ => le_rfl
  have hcross : ∀ i : ℕ, 0 < i → ∀ j : ℕ, i < j → freeHillValue i < freeHillValue j :=
    fun _ _ _ hij => strictMono_freeHillValue hij
  by_cases hx : ∃ n : ℕ, x = freeHillValue n
  · obtain ⟨n,rfl⟩ := hx
    by_cases hn : n = 0
    · subst n
      simp only [Nat.cast_zero]
      rw [hillHminusFreeLabels,singletonPairedEnumeration_count_initial _ _ _ hstart hpair,
        hillHminusRadicand_zero_eq_free]
      simpa only [freeHillValue,Int.cast_zero,mul_zero,zero_pow (by decide : (2:ℕ) ≠ 0),ofReal_zero] using
        hillL2Radicand_free_order_zero.symm
    · rw [hillHminusFreeLabels,singletonPairedEnumeration_count_pair _ _ _ hstart hpair hcross n
        (by omega) (freeHillValue n) ⟨le_rfl,le_rfl⟩,
        if_pos rfl,hillHminusRadicand_zero_eq_free,hillL2Radicand_free_order n (by omega)]
  · have hn (j : ℕ) : hillHminusFreeLabels j ≠ x := by
      intro hj
      have hz := (hillHminusFreeLabels_roots_iff (x:ℂ)).mpr ⟨j,by rw [hj]⟩
      obtain ⟨n,he⟩ := (hillL2Radicand_free_zero_iff (x:ℂ)).mp (hillHminusRadicand_zero_eq_free ▸ hz)
      exact hx ⟨n,Complex.ofReal_injective he⟩
    simp only [if_neg (hn _),finsum_zero]
    symm
    by_contra hne
    have hz := apply_eq_zero_of_analyticOrderNatAt_ne_zero hne
    obtain ⟨j,hj⟩ := (hillHminusFreeLabels_roots_iff (x:ℂ)).mp hz
    exact hn j (Complex.ofReal_injective hj).symm

theorem hillHminusLabels_eq_free (hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne)) :
    hillHminusLabels 0 hr = hillHminusFreeLabels := by
  apply ordered_nat_enumeration_eq_of_multiplicity _ _
    (hillHminusLabels_finite_fiber 0 hr) hillHminusFreeLabels_finite_fiber
    (monotone_hillHminusLabels 0 hr) monotone_hillHminusFreeLabels
  intro x
  rw [hillHminusLabels_global_multiplicity,hillHminusFreeLabels_global_multiplicity]

theorem hillHminusLabels_free_pair (hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne))
    (n : ℕ+) :
    hillHminusLabels 0 hr (2*(n:ℕ)-1) = freeHillValue (n:ℕ) ∧
      hillHminusLabels 0 hr (2*(n:ℕ)) = freeHillValue (n:ℕ) := by
  rw [hillHminusLabels_eq_free hr]
  exact ⟨singletonPairedEnumeration_left _ _ _ (n:ℕ) n.pos,
    singletonPairedEnumeration_right _ _ _ (n:ℕ) n.pos⟩

end NLS.KdV
