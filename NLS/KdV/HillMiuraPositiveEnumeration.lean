import NLS.KdV.HillMiuraPositiveGaps
import NLS.SequenceSpaces.SingletonPairedEnumeration
import NLS.ZakharovShabat.RealGapEndpointMultiplicity

/-! # The actual nonnegative Miura Dirac endpoint enumeration

Take the right endpoint at index zero and both endpoints at every
positive index. This retains exact algebraic multiplicities at every
positive spectral value, with no central cutoff or open-gap restriction.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.ZakharovShabat

def hillMiuraPositiveFrequencies (u : Coeff 2) : ℕ → ℝ :=
  singletonPairedEnumeration (hillMiuraDiracRight u 0).re
    (fun n => (hillMiuraDiracLeft u n).re) (fun n => (hillMiuraDiracRight u n).re)

theorem hillMiuraDirac_re_separated (u : PeriodOneRealL2) {i j : ℤ} (hij : i < j) :
    (hillMiuraDiracRight u.val i).re < (hillMiuraDiracLeft u.val j).re :=
  canonicalPeriodicRight_re_lt_left_of_lt (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
    (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) hij

theorem hillMiuraPositiveFrequencies_initial (u : Coeff 2) :
    hillMiuraPositiveFrequencies u 0 = (hillMiuraDiracRight u 0).re :=
  singletonPairedEnumeration_zero _ _ _

theorem hillMiuraPositiveFrequencies_left (u : Coeff 2) (n : ℕ) (hn : 0 < n) :
    hillMiuraPositiveFrequencies u (2*n-1) = (hillMiuraDiracLeft u n).re :=
  singletonPairedEnumeration_left _ _ _ n hn

theorem hillMiuraPositiveFrequencies_right (u : Coeff 2) (n : ℕ) (hn : 0 < n) :
    hillMiuraPositiveFrequencies u (2*n) = (hillMiuraDiracRight u n).re :=
  singletonPairedEnumeration_right _ _ _ n hn

theorem monotone_hillMiuraPositiveFrequencies (u : PeriodOneRealL2) :
    Monotone (hillMiuraPositiveFrequencies u.val) := by
  apply monotone_singletonPairedEnumeration
  · intro n hn
    exact hillMiuraDirac_re_separated u (by exact_mod_cast hn)
  · intro n _
    exact hillMiuraDiracPair_ordered u.val n
  · intro i _ j hij
    exact hillMiuraDirac_re_separated u (by exact_mod_cast hij)

theorem hillMiuraPositiveFrequencies_finite_fiber (u : PeriodOneRealL2) (x : ℝ) :
    {j : ℕ | hillMiuraPositiveFrequencies u.val j = x}.Finite := by
  apply singletonPairedEnumeration_finite_fiber
  · intro n hn
    exact hillMiuraDirac_re_separated u (by exact_mod_cast hn)
  · intro n _
    exact hillMiuraDiracPair_ordered u.val n
  · intro i _ j hij
    exact hillMiuraDirac_re_separated u (by exact_mod_cast hij)

theorem hillMiuraPositiveFrequencies_nonneg (u : PeriodOneRealL2) (j : ℕ) :
    0 ≤ hillMiuraPositiveFrequencies u.val j := by
  exact (hillMiura_gap_zero_contains_zero u).2.trans
    ((monotone_hillMiuraPositiveFrequencies u) (Nat.zero_le j))

theorem hillMiuraPositiveFrequencies_mem_spectrum (u : PeriodOneRealL2) (j : ℕ) :
    (hillMiuraPositiveFrequencies u.val j : ℂ) ∈
      periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) := by
  have hs (n : ℤ) := canonicalPeriodicEndpoints_mem_spectrum (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n
  have he (n : ℤ) :
      ((hillMiuraDiracLeft u.val n).re : ℂ) = hillMiuraDiracLeft u.val n ∧
      ((hillMiuraDiracRight u.val n).re : ℂ) = hillMiuraDiracRight u.val n := by
    have him := hillMiuraDiracPair_real u n
    exact ⟨Complex.ext rfl him.1.symm,Complex.ext rfl him.2.symm⟩
  by_cases hj : j = 0
  · subst j
    rw [hillMiuraPositiveFrequencies_initial,(he 0).2]
    exact (hs 0).2
  · obtain ⟨n,hn,hslot⟩ := singletonPairedEnumeration_slot j hj
    rcases hslot with rfl | rfl
    · rw [hillMiuraPositiveFrequencies_left u.val n hn,(he n).1]
      exact (hs n).1
    · rw [hillMiuraPositiveFrequencies_right u.val n hn,(he n).2]
      exact (hs n).2

theorem hillMiuraPositiveFrequencies_pos_of_zero_not_mem
    (u : PeriodOneRealL2)
    (hzero : (0 : ℂ) ∉ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val)))
    (j : ℕ) : 0 < hillMiuraPositiveFrequencies u.val j := by
  apply lt_of_le_of_ne (hillMiuraPositiveFrequencies_nonneg u j)
  intro he
  have hs := hillMiuraPositiveFrequencies_mem_spectrum u j
  rw [← he,ofReal_zero] at hs
  exact hzero hs

theorem hillMiuraPositiveFrequencies_exhaustive (u : PeriodOneRealL2) (x : ℝ) (hx : 0 < x) :
    (x : ℂ) ∈ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) ↔
      ∃ j : ℕ, hillMiuraPositiveFrequencies u.val j = x := by
  constructor
  · intro hs
    obtain ⟨n,hn⟩ := (canonicalPeriodicEndpoints_exhaustive (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) (x : ℂ)).mp hs
    have hn' : (hillMiuraDiracLeft u.val n).re = x ∨ (hillMiuraDiracRight u.val n).re = x := by
      rcases hn with h | h
      · exact Or.inl (congrArg Complex.re h)
      · exact Or.inr (congrArg Complex.re h)
    rcases lt_trichotomy n 0 with hneg | heq | hpos
    · have hr := hillMiura_negative_gap_right_neg u n hneg
      have hlr := hillMiuraDiracPair_ordered u.val n
      change (hillMiuraDiracRight u.val n).re < 0 at hr
      rcases hn' with h | h <;> linarith
    · subst n
      rcases hn' with h | h
      · have hl := (hillMiura_gap_zero_contains_zero u).1
        change (hillMiuraDiracLeft u.val 0).re ≤ 0 at hl
        linarith
      · exact ⟨0,(hillMiuraPositiveFrequencies_initial u.val).trans h⟩
    · have hnNat : 0 < n.toNat := by omega
      have hcast : (n.toNat : ℤ) = n := by omega
      rcases hn' with h | h
      · refine ⟨2*n.toNat-1,?_⟩
        rw [hillMiuraPositiveFrequencies_left u.val n.toNat hnNat,hcast]
        exact h
      · refine ⟨2*n.toNat,?_⟩
        rw [hillMiuraPositiveFrequencies_right u.val n.toNat hnNat,hcast]
        exact h
  · rintro ⟨j,rfl⟩
    exact hillMiuraPositiveFrequencies_mem_spectrum u j

theorem hillMiuraPositiveFrequencies_multiplicity (u : PeriodOneRealL2) (x : ℝ) (hx : 0 < x) :
    (∑ᶠ j : ℕ, if hillMiuraPositiveFrequencies u.val j = x then (1 : ℕ) else 0) =
      periodicAlgebraicMultiplicity (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) (x : ℂ) := by
  have hstart (n : ℕ) (hn : 0 < n) :
      (hillMiuraDiracRight u.val 0).re < (hillMiuraDiracLeft u.val n).re :=
    hillMiuraDirac_re_separated u (by exact_mod_cast hn)
  have hpair (n : ℕ) (_hn : 0 < n) :
      (hillMiuraDiracLeft u.val n).re ≤ (hillMiuraDiracRight u.val n).re :=
    hillMiuraDiracPair_ordered u.val n
  have hcross (i : ℕ) (_hi : 0 < i) (j : ℕ) (hij : i < j) :
      (hillMiuraDiracRight u.val i).re < (hillMiuraDiracLeft u.val j).re :=
    hillMiuraDirac_re_separated u (by exact_mod_cast hij)
  by_cases hspec : (x : ℂ) ∈ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val))
  · obtain ⟨j,hj⟩ := (hillMiuraPositiveFrequencies_exhaustive u x hx).mp hspec
    by_cases hj0 : j = 0
    · subst j
      have hx0 : (hillMiuraDiracRight u.val 0).re = x := (hillMiuraPositiveFrequencies_initial u.val).symm.trans hj
      have hwithin : x ∈ Icc (hillMiuraDiracLeft u.val 0).re (hillMiuraDiracRight u.val 0).re := by
        rw [← hx0]
        exact ⟨hillMiuraDiracPair_ordered u.val 0,le_rfl⟩
      have hm := periodicAlgebraicMultiplicity_eq_real_gap_endpoints (by simp) (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
        (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) 0 x hwithin
      have hleft : (hillMiuraDiracLeft u.val 0).re ≠ x := by
        have h := (hillMiura_gap_zero_contains_zero u).1
        change (hillMiuraDiracLeft u.val 0).re ≤ 0 at h
        linarith
      have hc := singletonPairedEnumeration_count_initial (hillMiuraDiracRight u.val 0).re
        (fun n => (hillMiuraDiracLeft u.val n).re) (fun n => (hillMiuraDiracRight u.val n).re) hstart hpair
      change periodicAlgebraicMultiplicity _ _ (x : ℂ) =
        (if (hillMiuraDiracLeft u.val 0).re = x then 1 else 0)+
        (if (hillMiuraDiracRight u.val 0).re = x then 1 else 0) at hm
      rw [if_neg hleft,if_pos hx0,zero_add] at hm
      rw [hm,← hx0]
      exact hc
    · obtain ⟨n,hn,_,hb⟩ := singletonPairedEnumeration_mem_pair
        (hillMiuraDiracRight u.val 0).re (fun n => (hillMiuraDiracLeft u.val n).re)
        (fun n => (hillMiuraDiracRight u.val n).re) hpair j hj0
      change hillMiuraPositiveFrequencies u.val j ∈ _ at hb
      rw [hj] at hb
      have hc := singletonPairedEnumeration_count_pair (hillMiuraDiracRight u.val 0).re
        (fun n => (hillMiuraDiracLeft u.val n).re) (fun n => (hillMiuraDiracRight u.val n).re)
        hstart hpair hcross n hn x hb
      have hm := periodicAlgebraicMultiplicity_eq_real_gap_endpoints (by simp) (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
        (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) (n : ℤ) x hb
      exact hc.trans hm.symm
  · have hn : ∀ j : ℕ, hillMiuraPositiveFrequencies u.val j ≠ x := by
      intro j hj
      exact hspec ((hillMiuraPositiveFrequencies_exhaustive u x hx).mpr ⟨j,hj⟩)
    simp only [if_neg (hn _),finsum_zero]
    symm
    apply Nat.eq_zero_of_not_pos
    exact fun h => hspec ((periodicAlgebraicMultiplicity_pos_iff _ _ _).mp h)

end NLS.KdV
