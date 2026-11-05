import NLS.KdV.HillHminusOneLabelUniqueness

/-! # Canonical real characteristic labels in H^-1

Uniqueness removes every choice of cutoff, local chart, central sorting
and high-disc radius. A prescribed finite head is described on one
common complex H^-1 neighborhood by the actual canonical labels.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped Classical
namespace NLS.KdV

theorem exists_hillHminus_intrinsic_labeling
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ lambda : ℕ → ℝ, ∃ N : ℕ, ∃ r : ℝ, HillHminusRealCharacteristicLabeling q N r lambda := by
  obtain ⟨N,r,lambda,h⟩ := exists_hillHminus_real_characteristic_labeling q hq
  exact ⟨lambda,N,r,h⟩

def hillHminusRealLabels (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) : ℕ → ℝ :=
  (exists_hillHminus_intrinsic_labeling q hq).choose

theorem hillHminusRealLabels_spec (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ N : ℕ, ∃ r : ℝ, HillHminusRealCharacteristicLabeling q N r (hillHminusRealLabels q hq) :=
  (exists_hillHminus_intrinsic_labeling q hq).choose_spec

theorem hillHminusRealLabels_congr (q p : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p) (he : q = p) :
    hillHminusRealLabels q hq = hillHminusRealLabels p hp := by
  subst p
  rfl

theorem HillHminusRealCharacteristicLabeling.eq_canonical
    {q : PeriodOneHminusOne} {N : ℕ} {r : ℝ} {lambda : ℕ → ℝ}
    (h : HillHminusRealCharacteristicLabeling q N r lambda) (hq : IsRealPeriodOneHminusOne q) :
    lambda = hillHminusRealLabels q hq := by
  obtain ⟨_,_,g⟩ := hillHminusRealLabels_spec q hq
  exact h.unique g

theorem exists_hillHminusRealLabels_common_spec (q : PeriodOneHminusOne) (L : ℕ) :
    ∃ N : ℕ, ∃ r : ℝ, ∃ V : Set PeriodOneHminusOne,
      L ≤ N ∧ 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ ha : IsRealPeriodOneHminusOne a,
        HillHminusRealCharacteristicLabeling a N r (hillHminusRealLabels a ha) := by
  obtain ⟨N,r,V,hL,hN,hV,hq,hlabels⟩ := exists_hillHminus_labelings_near q L
  refine ⟨N,r,V,hL,hN,hV,hq,?_⟩
  intro a ha hreal
  obtain ⟨lambda,h⟩ := hlabels a ha hreal
  rwa [h.eq_canonical hreal] at h

theorem monotone_hillHminusRealLabels (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    Monotone (hillHminusRealLabels q hq) := by
  obtain ⟨_,_,h⟩ := hillHminusRealLabels_spec q hq
  exact h.monotone

theorem hillHminusRealLabels_root_iff (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (z : ℂ) : hillHminusRadicand q z = 0 ↔ ∃ j : ℕ, z = (hillHminusRealLabels q hq j : ℂ) := by
  obtain ⟨_,_,h⟩ := hillHminusRealLabels_spec q hq
  exact h.roots z

theorem hillHminusRealLabels_root (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (j : ℕ) : hillHminusRadicand q (hillHminusRealLabels q hq j) = 0 :=
  (hillHminusRealLabels_root_iff q hq _).mpr ⟨j,rfl⟩

theorem finite_fiber_hillHminusRealLabels (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (x : ℝ) : {j | hillHminusRealLabels q hq j = x}.Finite := by
  obtain ⟨_,_,h⟩ := hillHminusRealLabels_spec q hq
  exact h.finite_fiber x

theorem multiplicity_hillHminusRealLabels (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (x : ℝ) :
    (∑ᶠ j : ℕ, if hillHminusRealLabels q hq j = x then (1 : ℕ) else 0) =
      analyticOrderNatAt (hillHminusRadicand q) x := by
  classical
  obtain ⟨_,_,h⟩ := hillHminusRealLabels_spec q hq
  exact (h.finite_support_and_multiplicity x).2

theorem hillHminusRealLabels_zero_eq_lowest (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : hillHminusRealLabels q hq 0 = hillHminusLowestRealRoot q hq := by
  apply hillHminusLowestRealRoot_eq_of_minimal q hq _ (hillHminusRealLabels_root q hq 0)
  intro z hz
  obtain ⟨j,hj⟩ := (hillHminusRealLabels_root_iff q hq z).mp hz
  rw [hj,ofReal_re]
  exact monotone_hillHminusRealLabels q hq (Nat.zero_le j)

end NLS.KdV
