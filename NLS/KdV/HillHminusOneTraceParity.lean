import NLS.KdV.HillHminusOneLabelContinuity
import NLS.KdV.HillHminusOneCanonicalFreeLabels
import Mathlib.Topology.Algebra.Field

/-! # Exact trace parity and strict bands for real H^-1 potentials

Continuity fixes every indexed endpoint trace along the actual straight
potential path. Opposite neighboring trace levels prevent band collapse.
The actual central multiplicities follow from the intrinsic enumeration.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped Classical
namespace NLS.KdV

theorem hillHminusRealLabels_trace_parity
    (q : PeriodOneHminusOne) (hreal : IsRealPeriodOneHminusOne q) (j : ℕ) :
    hillHminusDiscriminant q (hillHminusRealLabels q hreal j) = 2*(-1 : ℂ)^((j+1)/2) := by
  let Q : Icc (0 : ℝ) 1 → PeriodOneHminusOne := fun t => (t.val : ℂ) • q
  have hQ : Continuous Q := (Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const
  have hQr (t : Icc (0 : ℝ) 1) : IsRealPeriodOneHminusOne (Q t) := hreal.smul_real t.val
  let labels (t : Icc (0 : ℝ) 1) := hillHminusRealLabels (Q t) (hQr t) j
  let f : Icc (0 : ℝ) 1 → ℂ := fun t => hillHminusDiscriminant (Q t) (labels t)
  let C : ℂ := 2*(-1 : ℂ)^((j+1)/2)
  have hCne : C ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hCsq : C^2 = 4 := by
    have hp : ((-1 : ℂ)^((j+1)/2))^2 = 1 := by
      rw [← pow_mul,Nat.mul_comm ((j+1)/2) 2,pow_mul]
      norm_num
    simp only [C,mul_pow,hp]
    norm_num
  have hf : Continuous f := by
    have hc : Continuous (fun p : ℂ × PeriodOneHminusOne => hillHminusDiscriminant p.2 p.1) :=
      analyticOnNhd_hillHminusDiscriminant_joint.continuous
    have hl : Continuous labels := continuous_hillHminusRealLabels_family Q hQ hQr j
    have hm : Continuous (fun t : Icc (0 : ℝ) 1 => ((labels t : ℂ),Q t)) :=
      (Complex.continuous_ofReal.comp hl).prodMk hQ
    exact Continuous.comp (g := fun p : ℂ × PeriodOneHminusOne => hillHminusDiscriminant p.2 p.1)
      (f := fun t : Icc (0 : ℝ) 1 => ((labels t : ℂ),Q t)) hc hm
  have hsq : EqOn (f^2) ((fun _ : Icc (0 : ℝ) 1 => C)^2) univ := by
    intro t _
    change (f t)^2 = C^2
    rw [hCsq]
    exact sub_eq_zero.mp (hillHminusRealLabels_root (Q t) (hQr t) j)
  have hQ0 : Q (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1) = 0 := by simp [Q]
  have hQ1 : Q (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1) = q := by simp [Q]
  have hrzero : IsRealPeriodOneHminusOne 0 := by intro k; simp
  have h0 : f (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1) = C := by
    have hl := congrFun (hillHminusRealLabels_congr _ _ (hQr _) hrzero hQ0) j
    change hillHminusDiscriminant (Q _) (hillHminusRealLabels (Q _) (hQr _) j) = C
    rw [hl,hQ0]
    exact hillHminusRealLabels_zero_trace hrzero j
  have hconst := isPreconnected_univ.eq_of_sq_eq hf.continuousOn continuous_const.continuousOn hsq
    (fun _ => hCne) (mem_univ (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1)) h0
  have h1 := hconst (mem_univ (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1))
  have hf1 : f (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1) =
      hillHminusDiscriminant q (hillHminusRealLabels q hreal j) := by
    have hl := congrFun (hillHminusRealLabels_congr _ _ (hQr _) hreal hQ1) j
    change hillHminusDiscriminant (Q _) (hillHminusRealLabels (Q _) (hQr _) j) = _
    rw [hl,hQ1]
  exact hf1.symm.trans h1

theorem hillHminusRealLabels_pair_trace
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    hillHminusDiscriminant (q) (hillHminusRealLabels q hreal (2*n-1)) = 2*(-1 : ℂ)^n ∧
    hillHminusDiscriminant (q) (hillHminusRealLabels q hreal (2*n)) = 2*(-1 : ℂ)^n := by
  have hl := hillHminusRealLabels_trace_parity q hreal (2*n-1)
  have hr := hillHminusRealLabels_trace_parity q hreal (2*n)
  have hli : (2*n-1+1)/2 = n := by omega
  have hri : (2*n+1)/2 = n := by omega
  rw [hli] at hl
  rw [hri] at hr
  exact ⟨hl,hr⟩

/-- Strict separation of neighboring bands, allowing a closed gap inside
each pair of slots 2*n-1 and 2*n. -/
theorem hillHminusRealLabels_band_strict
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q) (n : ℕ) :
    hillHminusRealLabels q hreal (2*n) < hillHminusRealLabels q hreal (2*n+1) := by
  have hle := monotone_hillHminusRealLabels q hreal (show 2*n ≤ 2*n+1 by omega)
  apply lt_of_le_of_ne hle
  intro he
  have hp := hillHminusRealLabels_trace_parity q hreal (2*n)
  have hm := hillHminusRealLabels_trace_parity q hreal (2*n+1)
  have hn : (2*n+1)/2 = n := by omega
  have hn' : (2*n+1+1)/2 = n+1 := by omega
  rw [hn,he] at hp
  rw [hn'] at hm
  have hd := hp.symm.trans hm
  rw [pow_succ] at hd
  have hz : (2 : ℂ)*(-1 : ℂ)^n = 0 := by linear_combination hd/2
  exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (pow_ne_zero n (by norm_num))) hz

/-- The actual lowest characteristic energy is simple. -/
theorem hillHminusLowestRealRoot_order_one
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q) :
    analyticOrderNatAt (hillHminusRadicand (q)) (hillHminusLowestRealRoot q hreal) = 1 := by
  let L := hillHminusRealLabels q hreal
  have hs : Function.support (fun j : ℕ => if L j = L 0 then (1 : ℕ) else 0) ⊆ ({0} : Finset ℕ) := by
    intro j hj
    have he : L j = L 0 := by simpa using hj
    by_cases hj0 : j = 0
    · simpa only [Finset.mem_coe,Finset.mem_singleton] using hj0
    · have hh := monotone_hillHminusRealLabels q hreal (show 1 ≤ j by omega)
      have hstrict := hillHminusRealLabels_band_strict q hreal 0
      change L 0 < L 1 at hstrict
      change L 1 ≤ L j at hh
      rw [he] at hh
      linarith
  have hc := multiplicity_hillHminusRealLabels q hreal (L 0)
  change (∑ᶠ j : ℕ, if L j = L 0 then (1 : ℕ) else 0) = _ at hc
  rw [finsum_eq_sum_of_support_subset _ hs,Finset.sum_singleton,if_pos rfl] at hc
  simpa only [← hillHminusRealLabels_zero_eq_lowest] using hc.symm

/-- Each non-lowest characteristic root has exactly the multiplicity
recorded by its own two endpoint slots, even in the central spectrum. -/
theorem hillHminusRealLabels_pair_order
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q)
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x = hillHminusRealLabels q hreal (2*n-1) ∨ x = hillHminusRealLabels q hreal (2*n)) :
    analyticOrderNatAt (hillHminusRadicand (q)) x =
      ({hillHminusRealLabels q hreal (2*n-1),hillHminusRealLabels q hreal (2*n)} : Multiset ℝ).count x := by
  let L := hillHminusRealLabels q hreal
  have hab := monotone_hillHminusRealLabels q hreal (show 2*n-1 ≤ 2*n by omega)
  have hxl : L (2*n-1) ≤ x := by rcases hx with rfl | rfl; exact le_rfl; exact hab
  have hxr : x ≤ L (2*n) := by rcases hx with rfl | rfl; exact hab; exact le_rfl
  have hprev := hillHminusRealLabels_band_strict q hreal (n-1)
  have hpidx : 2*(n-1)+1 = 2*n-1 := by omega
  rw [hpidx] at hprev
  have hnext := hillHminusRealLabels_band_strict q hreal n
  have hs : Function.support (fun i : ℕ => if L i = x then (1 : ℕ) else 0) ⊆
      ({2*n-1,2*n} : Finset ℕ) := by
    intro i hi
    have he : L i = x := by simpa using hi
    by_cases hlow : i < 2*n-1
    · have hm := monotone_hillHminusRealLabels q hreal (show i ≤ 2*(n-1) by omega)
      change L i ≤ L (2*(n-1)) at hm
      change L (2*(n-1)) < L (2*n-1) at hprev
      rw [he] at hm
      linarith
    by_cases hhigh : 2*n < i
    · have hm := monotone_hillHminusRealLabels q hreal (show 2*n+1 ≤ i by omega)
      change L (2*n+1) ≤ L i at hm
      change L (2*n) < L (2*n+1) at hnext
      rw [he] at hm
      linarith
    · have he' : i = 2*n-1 ∨ i = 2*n := by omega
      simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using he'
  have hc := multiplicity_hillHminusRealLabels q hreal x
  change (∑ᶠ i : ℕ, if L i = x then (1 : ℕ) else 0) = _ at hc
  rw [finsum_eq_sum_of_support_subset _ hs,Finset.sum_pair (show 2*n-1 ≠ 2*n by omega)] at hc
  have hm : ({L (2*n-1),L (2*n)} : Multiset ℝ).count x =
      (if L (2*n-1) = x then 1 else 0)+(if L (2*n) = x then 1 else 0) := by
    simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,eq_comm,Nat.add_comm]
  exact hc.symm.trans hm.symm

theorem hillHminusRealLabels_open_gap_orders
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q)
    (n : ℕ) (hn : 1 ≤ n)
    (hopen : hillHminusRealLabels q hreal (2*n-1) ≠ hillHminusRealLabels q hreal (2*n)) :
    analyticOrderNatAt (hillHminusRadicand (q)) (hillHminusRealLabels q hreal (2*n-1)) = 1 ∧
    analyticOrderNatAt (hillHminusRadicand (q)) (hillHminusRealLabels q hreal (2*n)) = 1 := by
  constructor
  · rw [hillHminusRealLabels_pair_order q hreal n hn _ (Or.inl rfl)]
    simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,
      if_neg hopen,ite_true,zero_add]
  · rw [hillHminusRealLabels_pair_order q hreal n hn _ (Or.inr rfl)]
    simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,
      if_neg (Ne.symm hopen),ite_true,add_zero]

theorem hillHminusRealLabels_closed_gap_order
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q)
    (n : ℕ) (hn : 1 ≤ n)
    (hclosed : hillHminusRealLabels q hreal (2*n-1) = hillHminusRealLabels q hreal (2*n)) :
    analyticOrderNatAt (hillHminusRadicand (q))
      (hillHminusRealLabels q hreal (2*n-1)) = 2 := by
  rw [hillHminusRealLabels_pair_order q hreal n hn _ (Or.inl rfl),hclosed]
  simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,ite_true]

end NLS.KdV
