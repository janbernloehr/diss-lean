import NLS.KdV.HillLabelContinuity
import NLS.KdV.HillCanonicalFreeLabels
import Mathlib.Topology.Algebra.Field

/-! # Physical trace parity and strict real Hill band ordering

Continuity of the actual ordered labels fixes their trace level along
the straight real potential segment. Adjacent bands have opposite trace
levels, so their endpoints are strictly separated. In particular the
lowest actual characteristic root has analytic order one.
-/

noncomputable section
open Set Filter Topology
open scoped Classical
namespace NLS.KdV

theorem hillRealLabels_trace_parity
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (j : ℕ) :
    hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillRealLabels q hq hreal j) =
      2*(-1 : ℂ)^((j+1)/2) := by
  let Q : Icc (0 : ℝ) 1 → WeightedCoeff SpectralWeight.one.toWeight 2 := fun t => (t.val : ℂ) • q
  have hQ : Continuous Q := (Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const
  have hqp (t : Icc (0 : ℝ) 1) : SpectralWeight.one.toCoeff (Q t) ∈ Coeff.paritySubspace 0 := by
    rw [map_smul]
    exact (Coeff.paritySubspace 0).smul_mem _ hq
  have hQr (t : Icc (0 : ℝ) 1) : IsRealHillPotential (SpectralWeight.one.toCoeff (Q t)) := by
    rw [map_smul]
    exact hreal.smul_real t.val
  let labels (t : Icc (0 : ℝ) 1) := hillRealLabels (Q t) (hqp t) (hQr t) j
  let f : Icc (0 : ℝ) 1 → ℂ := fun t =>
    hillL2Discriminant (SpectralWeight.one.toCoeff (Q t)) (labels t)
  let C : ℂ := 2*(-1 : ℂ)^((j+1)/2)
  have hCne : C ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hCsq : C^2 = 4 := by
    have hp : ((-1 : ℂ)^((j+1)/2))^2 = 1 := by
      rw [← pow_mul, Nat.mul_comm ((j+1)/2) 2, pow_mul]
      norm_num
    simp only [C,mul_pow,hp]
    norm_num
  have hf : Continuous f := by
    have hc : Continuous (fun p : ℂ × Coeff 2 => hillL2Discriminant p.2 p.1) :=
      continuous_iff_continuousAt.mpr
        (fun p => (analyticOnNhd_hillL2Discriminant_joint p (mem_univ _)).continuousAt)
    have hl : Continuous labels := continuous_hillRealLabels_family Q hQ hqp hQr j
    have hm : Continuous (fun t : Icc (0 : ℝ) 1 =>
        ((labels t : ℂ),SpectralWeight.one.toCoeff (Q t))) :=
      (Complex.continuous_ofReal.comp hl).prodMk (SpectralWeight.one.toCoeff.continuous.comp hQ)
    convert! hc.comp hm using 1
  have hsq : EqOn (f^2) ((fun _ : Icc (0 : ℝ) 1 => C)^2) univ := by
    intro t _
    change (f t)^2 = C^2
    rw [hCsq]
    exact sub_eq_zero.mp ((hillRealLabels_spec (Q t) (hqp t) (hQr t)).root j)
  have hQ0 : Q (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1) = 0 := by simp [Q]
  have hQ1 : Q (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1) = q := by simp [Q]
  have hzero : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈
      Coeff.paritySubspace 0 := by simp
  have hrzero : IsRealHillPotential
      (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    intro k
    simp
  have h0 : f (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1) = C := by
    have hl := congrFun (hillRealLabels_congr _ _ (hqp _) hzero (hQr _) hrzero hQ0) j
    change hillL2Discriminant (SpectralWeight.one.toCoeff (Q _))
      (hillRealLabels (Q _) (hqp _) (hQr _) j) = C
    rw [hl,hQ0,map_zero]
    exact hillRealLabels_zero_trace hzero hrzero j
  have hconst := isPreconnected_univ.eq_of_sq_eq hf.continuousOn continuous_const.continuousOn hsq
    (fun _ => hCne) (mem_univ (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1)) h0
  have h1 := hconst (mem_univ (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1))
  have hf1 : f (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1) =
      hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillRealLabels q hq hreal j) := by
    have hl := congrFun (hillRealLabels_congr _ _ (hqp _) hq (hQr _) hreal hQ1) j
    change hillL2Discriminant (SpectralWeight.one.toCoeff (Q _))
      (hillRealLabels (Q _) (hqp _) (hQr _) j) = _
    rw [hl,hQ1]
  exact hf1.symm.trans h1

theorem hillRealLabels_pair_trace
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillRealLabels q hq hreal (2*n-1)) = 2*(-1 : ℂ)^n ∧
    hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillRealLabels q hq hreal (2*n)) = 2*(-1 : ℂ)^n := by
  have hl := hillRealLabels_trace_parity q hq hreal (2*n-1)
  have hr := hillRealLabels_trace_parity q hq hreal (2*n)
  have hli : (2*n-1+1)/2 = n := by omega
  have hri : (2*n+1)/2 = n := by omega
  rw [hli] at hl
  rw [hri] at hr
  exact ⟨hl,hr⟩

/-- Strict separation of neighboring bands, allowing a closed gap inside
each pair of slots 2*n-1 and 2*n. -/
theorem hillRealLabels_band_strict
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) :
    hillRealLabels q hq hreal (2*n) < hillRealLabels q hq hreal (2*n+1) := by
  have hle := monotone_hillRealLabels q hq hreal (show 2*n ≤ 2*n+1 by omega)
  apply lt_of_le_of_ne hle
  intro he
  have hp := hillRealLabels_trace_parity q hq hreal (2*n)
  have hm := hillRealLabels_trace_parity q hq hreal (2*n+1)
  have hn : (2*n+1)/2 = n := by omega
  have hn' : (2*n+1+1)/2 = n+1 := by omega
  rw [hn,he] at hp
  rw [hn'] at hm
  have hd := hp.symm.trans hm
  rw [pow_succ] at hd
  have hz : (2 : ℂ)*(-1 : ℂ)^n = 0 := by linear_combination hd/2
  exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (pow_ne_zero n (by norm_num))) hz

/-- The actual lowest characteristic energy is simple. -/
theorem hillLowestEnergy_order_one
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) (hillLowestEnergy q hq hreal) = 1 := by
  let L := hillRealLabels q hq hreal
  have hs : Function.support (fun j : ℕ => if L j = L 0 then (1 : ℕ) else 0) ⊆ ({0} : Finset ℕ) := by
    intro j hj
    have he : L j = L 0 := by simpa using hj
    by_cases hj0 : j = 0
    · simpa only [Finset.mem_coe,Finset.mem_singleton] using hj0
    · have hh := monotone_hillRealLabels q hq hreal (show 1 ≤ j by omega)
      have hstrict := hillRealLabels_band_strict q hq hreal 0
      change L 0 < L 1 at hstrict
      change L 1 ≤ L j at hh
      rw [he] at hh
      linarith
  have hc := (hillRealLabels_global_multiplicity q hq hreal (L 0)).2
  change (∑ᶠ j : ℕ, if L j = L 0 then (1 : ℕ) else 0) = _ at hc
  rw [finsum_eq_sum_of_support_subset _ hs,Finset.sum_singleton,if_pos rfl] at hc
  exact hc.symm

/-- Each non-lowest characteristic root has exactly the multiplicity
recorded by its own two endpoint slots, even in the central spectrum. -/
theorem hillRealLabels_pair_order
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x = hillRealLabels q hq hreal (2*n-1) ∨ x = hillRealLabels q hq hreal (2*n)) :
    analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) x =
      ({hillRealLabels q hq hreal (2*n-1),hillRealLabels q hq hreal (2*n)} : Multiset ℝ).count x := by
  let L := hillRealLabels q hq hreal
  have hab := monotone_hillRealLabels q hq hreal (show 2*n-1 ≤ 2*n by omega)
  have hxl : L (2*n-1) ≤ x := by rcases hx with rfl | rfl; exact le_rfl; exact hab
  have hxr : x ≤ L (2*n) := by rcases hx with rfl | rfl; exact hab; exact le_rfl
  have hprev := hillRealLabels_band_strict q hq hreal (n-1)
  have hpidx : 2*(n-1)+1 = 2*n-1 := by omega
  rw [hpidx] at hprev
  have hnext := hillRealLabels_band_strict q hq hreal n
  have hs : Function.support (fun i : ℕ => if L i = x then (1 : ℕ) else 0) ⊆
      ({2*n-1,2*n} : Finset ℕ) := by
    intro i hi
    have he : L i = x := by simpa using hi
    by_cases hlow : i < 2*n-1
    · have hm := monotone_hillRealLabels q hq hreal (show i ≤ 2*(n-1) by omega)
      change L i ≤ L (2*(n-1)) at hm
      change L (2*(n-1)) < L (2*n-1) at hprev
      rw [he] at hm
      linarith
    by_cases hhigh : 2*n < i
    · have hm := monotone_hillRealLabels q hq hreal (show 2*n+1 ≤ i by omega)
      change L (2*n+1) ≤ L i at hm
      change L (2*n) < L (2*n+1) at hnext
      rw [he] at hm
      linarith
    · have he' : i = 2*n-1 ∨ i = 2*n := by omega
      simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using he'
  have hc := (hillRealLabels_global_multiplicity q hq hreal x).2
  change (∑ᶠ i : ℕ, if L i = x then (1 : ℕ) else 0) = _ at hc
  rw [finsum_eq_sum_of_support_subset _ hs,Finset.sum_pair (show 2*n-1 ≠ 2*n by omega)] at hc
  have hm : ({L (2*n-1),L (2*n)} : Multiset ℝ).count x =
      (if L (2*n-1) = x then 1 else 0)+(if L (2*n) = x then 1 else 0) := by
    simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,eq_comm,Nat.add_comm]
  exact hc.symm.trans hm.symm

theorem hillRealLabels_open_gap_orders
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n)
    (hopen : hillRealLabels q hq hreal (2*n-1) ≠ hillRealLabels q hq hreal (2*n)) :
    analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) (hillRealLabels q hq hreal (2*n-1)) = 1 ∧
    analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) (hillRealLabels q hq hreal (2*n)) = 1 := by
  constructor
  · rw [hillRealLabels_pair_order q hq hreal n hn _ (Or.inl rfl)]
    simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,
      if_neg hopen,ite_true,zero_add]
  · rw [hillRealLabels_pair_order q hq hreal n hn _ (Or.inr rfl)]
    simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,
      if_neg (Ne.symm hopen),ite_true,add_zero]

theorem hillRealLabels_closed_gap_order
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n)
    (hclosed : hillRealLabels q hq hreal (2*n-1) = hillRealLabels q hq hreal (2*n)) :
    analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (hillRealLabels q hq hreal (2*n-1)) = 2 := by
  rw [hillRealLabels_pair_order q hq hreal n hn _ (Or.inl rfl),hclosed]
  simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,ite_true]

end NLS.KdV
