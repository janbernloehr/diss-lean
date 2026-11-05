import NLS.MKdV.MiuraSpectralActions
import NLS.MKdV.MiuraActionReflection
import NLS.MKdV.NativeMiuraHillHamiltonian
import NLS.ZakharovShabat.SourceFiniteGapNLSHamiltonians

/-! # Finite-gap Miura profiles and their physical Hamiltonians

Finite-gap is defined by the independently labeled physical Hill gaps.
It is equivalent to finite support of the actual mKdV contour actions
and to finite-gap of the original diagonal NLS source. The latter gives
a smooth Fourier representative, with every original coefficient intact.
-/
noncomputable section
open Set Complex NLS.Fourier NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate ContDiff
namespace NLS.MKdV

def miuraFiniteGap (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) : Prop :=
  {n : ℕ | 1 ≤ n ∧ miuraHillLabels a ha (2*n-1) ≠ miuraHillLabels a ha (2*n)}.Finite

theorem miuraFiniteGap_iff_action_support (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    miuraFiniteGap a ha ↔ {n : ℕ | 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0}.Finite := by
  have he : {n : ℕ | 1 ≤ n ∧ miuraHillLabels a ha (2*n-1) ≠ miuraHillLabels a ha (2*n)} =
      {n : ℕ | 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0} := by
    ext n
    constructor
    · rintro ⟨hn,hg⟩
      exact ⟨hn,fun h => hg ((miuraNLSAction_zero_iff_hillGap_collapsed a ha n hn).mp
        ((miuraMKdVAction_nonnegative_and_zero_iff a ha n hn).2.2.mp h))⟩
    · rintro ⟨hn,hg⟩
      exact ⟨hn,fun h => hg ((miuraMKdVAction_nonnegative_and_zero_iff a ha n hn).2.2.mpr
        ((miuraNLSAction_zero_iff_hillGap_collapsed a ha n hn).mpr h))⟩
  exact he ▸ Iff.rfl

theorem miuraFiniteGap_iff_sourceFiniteGap (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    miuraFiniteGap a ha ↔ realDiagonalH1Source a ha ∈
      sourceFiniteGapLocus (by simp) (by norm_num) := by
  have hg (n : ℤ) : miuraNLSAction a n = 0 ↔
      canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (realDiagonalH1Source a ha).val) (periodOnePotential_mem _) n = 0 := by
    change miuraNLSAction a n = 0 ↔ miuraNLSRight a n-miuraNLSLeft a n = 0
    rw [miuraNLSAction_zero_iff_endpoints a ha n,sub_eq_zero]
    exact eq_comm
  have hs : {n : ℤ | miuraNLSAction a n ≠ 0} =
      {n : ℤ | canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (realDiagonalH1Source a ha).val) (periodOnePotential_mem _) n ≠ 0} := by
    ext n
    exact not_congr (hg n)
  have hn (n : ℕ) (h : 1 ≤ n) :
      miuraHillLabels a ha (2*n-1) ≠ miuraHillLabels a ha (2*n) ↔ miuraNLSAction a n ≠ 0 :=
    (not_congr (miuraNLSAction_zero_iff_hillGap_collapsed a ha n h)).symm
  change _ ↔ {n : ℤ | canonicalPeriodicGap _ _ _ _ n ≠ 0}.Finite
  rw [← hs]
  constructor
  · intro hf
    have hbound : {n : ℤ | miuraNLSAction a n ≠ 0} ⊆
        {0} ∪ (Int.ofNat '' {n : ℕ | 1 ≤ n ∧ miuraHillLabels a ha (2*n-1) ≠ miuraHillLabels a ha (2*n)}) ∪
          ((fun n : ℕ => -(n : ℤ)) ''
            {n : ℕ | 1 ≤ n ∧ miuraHillLabels a ha (2*n-1) ≠ miuraHillLabels a ha (2*n)}) := by
      intro n hne
      change miuraNLSAction a n ≠ 0 at hne
      by_cases hz : n = 0
      · exact Or.inl (Or.inl (by simpa only [mem_singleton_iff] using hz))
      by_cases hp : 0 < n
      · have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hp.le
        have hnat : 1 ≤ n.toNat := by omega
        exact Or.inl (Or.inr ⟨n.toNat,⟨hnat,(hn _ hnat).mpr (by simpa only [he] using hne)⟩,he⟩)
      · have hm : 0 < -n := by omega
        have he : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg hm.le
        have hnat : 1 ≤ (-n).toNat := by omega
        refine Or.inr ⟨(-n).toNat,⟨hnat,(hn _ hnat).mpr ?_⟩,by dsimp only; rw [he,neg_neg]⟩
        simpa only [he,miuraNLSAction_reflection a ha n] using hne
    exact (((finite_singleton 0).union (hf.image Int.ofNat)).union
      (hf.image (fun n : ℕ => -(n : ℤ)))).subset hbound
  · intro hf
    apply (hf.preimage (show Function.Injective (fun n : ℕ => (n : ℤ)) from Int.ofNat_injective).injOn).subset
    rintro n ⟨hnat,hne⟩
    exact (hn n hnat).mp hne

def miuraFiniteGapProfile (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    (hf : miuraFiniteGap a ha) : ℝ → ℂ :=
  (sourceFiniteGapPhysicalPair (by simp) (by norm_num) (realDiagonalH1Source a ha)
    ((miuraFiniteGap_iff_sourceFiniteGap a ha).mp hf)).1

theorem sourceFiniteGapPhysicalPair_diagonal (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) :
    sourceFiniteGapPhysicalPair (by simp) (by norm_num) (realDiagonalH1Source a ha)
      ((miuraFiniteGap_iff_sourceFiniteGap a ha).mp hf) =
        (miuraFiniteGapProfile a ha hf,miuraFiniteGapProfile a ha hf) := by
  apply Prod.ext
  · rfl
  · change periodOneSynthesis _ = periodOneSynthesis _
    congr 1

theorem miuraFiniteGapProfile_smooth_periodic (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) :
    ContDiff ℝ ∞ (miuraFiniteGapProfile a ha hf) ∧ Function.Periodic (miuraFiniteGapProfile a ha hf) 1 :=
  ⟨(contDiff_sourceFiniteGapPhysicalPair _ _ _ _).1,
    (periodic_sourceFiniteGapPhysicalPair _ _ _ _).1⟩

theorem periodOneCoefficient_miuraFiniteGapProfile (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) (n : ℤ) :
    periodOneCoefficient (miuraFiniteGapProfile a ha hf) n = a.val n := by
  simpa only [miuraFiniteGapProfile,realDiagonalH1Source,sobolevSourceInclusion_fst] using
    (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num)
      (realDiagonalH1Source a ha) ((miuraFiniteGap_iff_sourceFiniteGap a ha).mp hf) n).1

/-- The original finite-gap coefficients lie in every native scalar domain;
this construction changes none of them. -/
def miuraFiniteGapSobolev (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) (s : ℕ) : ScalarSobolev s :=
  ⟨a.val,by
    change Memℓp (fun n => (Weight.sobolev (s : ℝ) n : ℂ)*a.val n) 2
    have h := (sourceFiniteGap_mem_all_sobolev (by simp) (by norm_num)
      (realDiagonalH1Source a ha) ((miuraFiniteGap_iff_sourceFiniteGap a ha).mp hf)
        (s : ℝ) (Nat.cast_nonneg s)).1
    simpa only [realDiagonalH1Source,sobolevSourceInclusion_fst] using h⟩

@[simp] theorem miuraFiniteGapSobolev_apply (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) (s : ℕ) (n : ℤ) :
    (miuraFiniteGapSobolev a ha hf s).val n = a.val n := rfl

theorem sourceFiniteGapHamiltonians_miura (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) (m : ℕ) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (realDiagonalH1Source a ha)
        ((miuraFiniteGap_iff_sourceFiniteGap a ha).mp hf) (2*m+1) =
          2*classicalMiuraHillHamiltonian (miuraFiniteGapProfile a ha hf) (m+1) ∧
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (realDiagonalH1Source a ha)
        ((miuraFiniteGap_iff_sourceFiniteGap a ha).mp hf) (2*m+2) = 0 := by
  simp only [sourceFiniteGapNLSHamiltonian]
  have hp := miuraFiniteGapProfile_smooth_periodic a ha hf
  exact ⟨classicalNLSHamiltonian_odd_diagonal_eq_miuraHill _ hp.1 hp.2 m,
    classicalNLSHamiltonian_even_diagonal_eq_zero _ hp.1 hp.2 m⟩

theorem nativeMiuraHillHamiltonian_eq_finiteGapProfile (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha)
    (s : ℕ) (u : ScalarSobolev s) (hc : ∀ n, u.val n = a.val n) :
    nativeMiuraHillHamiltonian s u = classicalMiuraHillHamiltonian (miuraFiniteGapProfile a ha hf) (s+1) := by
  have hp := miuraFiniteGapProfile_smooth_periodic a ha hf
  exact nativeMiuraHillHamiltonian_eq_classical s u _ hp.1 hp.2
    (fun n => (hc n).trans (periodOneCoefficient_miuraFiniteGapProfile a ha hf n).symm)

/-- The physical finite-gap calibration uses K on its complete native
domain, including the L² mass member. -/
theorem sourceFiniteGapHamiltonians_miura_native (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) (m : ℕ) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (realDiagonalH1Source a ha)
        ((miuraFiniteGap_iff_sourceFiniteGap a ha).mp hf) (2*m+1) =
          2*nativeMiuraHillHamiltonian m (miuraFiniteGapSobolev a ha hf m) ∧
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (realDiagonalH1Source a ha)
        ((miuraFiniteGap_iff_sourceFiniteGap a ha).mp hf) (2*m+2) = 0 := by
  rw [nativeMiuraHillHamiltonian_eq_finiteGapProfile a ha hf m _ (fun _ => rfl)]
  exact sourceFiniteGapHamiltonians_miura a ha hf m

end NLS.MKdV
