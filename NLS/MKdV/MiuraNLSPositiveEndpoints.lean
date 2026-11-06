import NLS.MKdV.MiuraHillSpectralIdentification
import NLS.ZakharovShabat.CanonicalPeriodicEvenReflection
import NLS.ZakharovShabat.CanonicalPeriodicGapOrder
import NLS.SequenceSpaces.OrderedOneSidedEnumeration

/-! # The exact positive half of the original NLS endpoint sequence

The actual Miura characteristic is even. Ordered l2 uniqueness therefore
fixes every negative index, including the central pair. On the real H¹
slice the positive sequence starts at lambda_0^+ and then lists the two
endpoints at each positive index, in their original order.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraNLSLeft (a : ScalarDomain 2) : ℤ → ℂ :=
  canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion (a,a)))
    (periodOnePotential_mem _)

def miuraNLSRight (a : ScalarDomain 2) : ℤ → ℂ :=
  canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion (a,a)))
    (periodOnePotential_mem _)

theorem canonicalPeriodicProduct_miura (a : ScalarDomain 2) (z : ℂ) :
    canonicalPeriodicProduct (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) z =
      hillL2Radicand (sobolevMiuraHillPotential a) (z^2) := by
  rw [canonicalPeriodic_eq_discriminant_sq_sub_four _ (periodOnePotential_mem _)]
  exact congrArg (fun d : ℂ => d^2-4) (hillL2Discriminant_miura_eq_canonical a z).symm

theorem miuraNLSEndpoints_reflection (a : ScalarDomain 2) (n : ℤ) :
    miuraNLSLeft a n = -miuraNLSRight a (-n) ∧ miuraNLSRight a n = -miuraNLSLeft a (-n) := by
  apply canonicalPeriodicEndpoints_neg_of_even _ (periodOnePotential_mem _) _ n
  intro z
  rw [canonicalPeriodicProduct_miura,canonicalPeriodicProduct_miura,neg_sq]

theorem miuraNLSEndpoints_real (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℤ) :
    (miuraNLSLeft a n).im = 0 ∧ (miuraNLSRight a n).im = 0 :=
  canonicalPeriodicEndpoints_im_eq_zero_of_realType (by simp) (by norm_num) _ (periodOnePotential_mem _)
    (isRealType_periodOnePotential (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property) n

theorem miuraNLSEndpoints_within (a : ScalarDomain 2) (n : ℤ) :
    (miuraNLSLeft a n).re ≤ (miuraNLSRight a n).re :=
  re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec (by simp) (by norm_num) _
    (periodOnePotential_mem (sobolevSourceInclusion (a,a)))).2.1 n)

theorem miuraNLSEndpoints_between (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    {i j : ℤ} (hij : i < j) : (miuraNLSRight a i).re < (miuraNLSLeft a j).re :=
  canonicalPeriodicRight_re_lt_left_of_lt (by simp) (by norm_num) _ (periodOnePotential_mem _)
    (isRealType_periodOnePotential (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property) hij

theorem miuraNLSRight_zero_nonnegative (a : ScalarDomain 2) : 0 ≤ (miuraNLSRight a 0).re := by
  have h := congrArg Complex.re (miuraNLSEndpoints_reflection a 0).1
  simp only [neg_zero,neg_re] at h
  have hw := miuraNLSEndpoints_within a 0
  linarith

theorem miuraNLSLeft_pos (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    {n : ℤ} (hn : 0 < n) : 0 < (miuraNLSLeft a n).re :=
  (miuraNLSRight_zero_nonnegative a).trans_lt (miuraNLSEndpoints_between a ha hn)

def miuraPositiveFrequency (a : ScalarDomain 2) : ℕ → ℝ :=
  appendPairedTail 1 (fun _ => (miuraNLSRight a 0).re)
    (fun n => (miuraNLSLeft a (n+1)).re) (fun n => (miuraNLSRight a (n+1)).re)

@[simp] theorem miuraPositiveFrequency_zero (a : ScalarDomain 2) :
    miuraPositiveFrequency a 0 = (miuraNLSRight a 0).re :=
  appendPairedTail_prefix _ _ _ _ _ (by norm_num)

theorem miuraPositiveFrequency_odd (a : ScalarDomain 2) (n : ℕ) :
    miuraPositiveFrequency a (2*n+1) = (miuraNLSLeft a (n+1)).re := by
  simpa only [miuraPositiveFrequency,add_comm 1] using appendPairedTail_even 1
    (fun _ => (miuraNLSRight a 0).re) (fun k => (miuraNLSLeft a (k+1)).re)
    (fun k => (miuraNLSRight a (k+1)).re) n

theorem miuraPositiveFrequency_even (a : ScalarDomain 2) (n : ℕ) :
    miuraPositiveFrequency a (2*n+2) = (miuraNLSRight a (n+1)).re := by
  have he : 1+2*n+1 = 2*n+2 := by omega
  simpa only [miuraPositiveFrequency,he] using appendPairedTail_odd 1
    (fun _ => (miuraNLSRight a 0).re) (fun k => (miuraNLSLeft a (k+1)).re)
    (fun k => (miuraNLSRight a (k+1)).re) n

theorem monotone_miuraPositiveFrequency (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) :
    Monotone (miuraPositiveFrequency a) := by
  apply monotone_appendPairedTail
  · intro i _ j _ _
    exact le_rfl
  · intro n
    exact miuraNLSEndpoints_within a _
  · intro n
    exact (miuraNLSEndpoints_between a ha (show (n+1 : ℤ) < (n+1+1 : ℕ) by omega)).le
  · intro j _
    exact (miuraNLSEndpoints_between a ha (show (0 : ℤ) < (0+1 : ℕ) by norm_num)).le

theorem miuraPositiveFrequency_nonnegative (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (j : ℕ) : 0 ≤ miuraPositiveFrequency a j := by
  have h := monotone_miuraPositiveFrequency a ha (Nat.zero_le j)
  rw [miuraPositiveFrequency_zero] at h
  exact (miuraNLSRight_zero_nonnegative a).trans h

theorem miuraNLSRight_neg (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    {n : ℤ} (hn : n < 0) : (miuraNLSRight a n).re < 0 := by
  have h := congrArg Complex.re (miuraNLSEndpoints_reflection a n).2
  simp only [neg_re] at h
  have hp := miuraNLSLeft_pos a ha (show 0 < -n by omega)
  linarith

theorem miuraPositiveFrequency_endpoint (a : ScalarDomain 2) (j : ℕ) :
    miuraPositiveFrequency a j = (miuraNLSLeft a ((j+1)/2 : ℕ)).re ∨
      miuraPositiveFrequency a j = (miuraNLSRight a ((j+1)/2 : ℕ)).re := by
  by_cases hj : j = 0
  · subst j
    exact Or.inr (miuraPositiveFrequency_zero a)
  · have he : j = 2*((j-1)/2)+1 ∨ j = 2*((j-1)/2)+2 := by omega
    rcases he with he | he
    · left
      rw [he,miuraPositiveFrequency_odd]
      have hi : (2*((j-1)/2)+1+1)/2 = (j-1)/2+1 := by omega
      rw [hi]
      simp only [Nat.cast_add,Nat.cast_one]
    · right
      rw [he,miuraPositiveFrequency_even]
      have hi : (2*((j-1)/2)+2+1)/2 = (j-1)/2+1 := by omega
      rw [hi]
      simp only [Nat.cast_add,Nat.cast_one]

theorem miuraPositiveFrequency_pos (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    {j : ℕ} (hj : 0 < j) : 0 < miuraPositiveFrequency a j := by
  have hn : (0 : ℤ) < ((j+1)/2 : ℕ) := by omega
  rcases miuraPositiveFrequency_endpoint a j with h | h
  · rw [h]
    exact miuraNLSLeft_pos a ha hn
  · rw [h]
    exact (miuraNLSLeft_pos a ha hn).trans_le (miuraNLSEndpoints_within a _)

theorem miuraPositiveFrequency_left (a : ScalarDomain 2) (n : ℕ) (hn : 1 ≤ n) :
    miuraPositiveFrequency a (2*n-1) = (miuraNLSLeft a n).re := by
  have he : 2*n-1 = 2*(n-1)+1 := by omega
  rw [he,miuraPositiveFrequency_odd]
  congr 2
  omega

theorem miuraPositiveFrequency_right (a : ScalarDomain 2) (n : ℕ) (hn : 1 ≤ n) :
    miuraPositiveFrequency a (2*n) = (miuraNLSRight a n).re := by
  have he : 2*n = 2*(n-1)+2 := by omega
  rw [he,miuraPositiveFrequency_even]
  congr 2
  omega

theorem miuraNLSEndpoint_index_unique (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    {m n : ℤ} {x : ℝ}
    (hm : (miuraNLSLeft a m).re = x ∨ (miuraNLSRight a m).re = x)
    (hn : (miuraNLSLeft a n).re = x ∨ (miuraNLSRight a n).re = x) : m = n := by
  have hb (k : ℤ) (hk : (miuraNLSLeft a k).re = x ∨ (miuraNLSRight a k).re = x) :
      (miuraNLSLeft a k).re ≤ x ∧ x ≤ (miuraNLSRight a k).re := by
    have hw := miuraNLSEndpoints_within a k
    rcases hk with hk | hk <;> constructor <;> linarith
  by_contra he
  have hm' := hb m hm
  have hn' := hb n hn
  rcases lt_or_gt_of_ne he with h | h
  · have hs := miuraNLSEndpoints_between a ha h
    linarith
  · have hs := miuraNLSEndpoints_between a ha h
    linarith

end NLS.MKdV
