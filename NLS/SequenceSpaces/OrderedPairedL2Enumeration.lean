import NLS.SequenceSpaces.OrderedPairedUnique
import NLS.SequenceSpaces.CoefficientDecay
import NLS.ComplexAnalysis.LexicographicOrder
import Mathlib.Algebra.BigOperators.Finprod

/-! # Uniqueness of ordered paired l2 enumerations

Common real strips isolate finite blocks. Global multiplicities and l2
displacements then determine both ordered coordinates without choosing
distant branches, even at repeated or collapsed pairs.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS

/-- A vertical strip separating a finite central block from the signed free-lattice tails. -/
def rootCentralStrip (K : ℕ) : Set ℂ := {z | |z.re| < Real.pi*K+Real.pi/2}

/-- Ordering and small tail displacements put exactly the central indices inside the strip. -/
theorem ordered_pair_centralStrip (ξ η : ℤ → ℂ) (K : ℕ)
    (hw : ∀ n, complexLexLE (ξ n) (η n))
    (hc : ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j))
    (hx : ∀ n : ℤ, K ≤ n.natAbs → ‖ξ n-(Real.pi:ℂ)*n‖ < Real.pi/4)
    (hy : ∀ n : ℤ, K ≤ n.natAbs → ‖η n-(Real.pi:ℂ)*n‖ < Real.pi/4) :
    (∀ n : ℤ, n.natAbs ≤ K → ξ n ∈ rootCentralStrip K ∧ η n ∈ rootCentralStrip K) ∧
    (∀ n : ℤ, K < n.natAbs → ξ n ∉ rootCentralStrip K ∧ η n ∉ rootCentralStrip K) := by
  have hxr (n : ℤ) (hn : K ≤ n.natAbs) : |(ξ n).re-Real.pi*n| < Real.pi/4 := by
    simpa using (Complex.abs_re_le_norm (ξ n-(Real.pi:ℂ)*n)).trans_lt (hx n hn)
  have hyr (n : ℤ) (hn : K ≤ n.natAbs) : |(η n).re-Real.pi*n| < Real.pi/4 := by
    simpa using (Complex.abs_re_le_norm (η n-(Real.pi:ℂ)*n)).trans_lt (hy n hn)
  constructor
  · intro n hn
    have hlow := (abs_lt.mp (hxr (-(K:ℤ)) (by simp))).1
    have hhigh := (abs_lt.mp (hyr (K:ℤ) (by simp))).2
    simp only [Int.cast_neg,Int.cast_natCast] at hlow hhigh
    have hleft : (ξ (-(K:ℤ))).re ≤ (ξ n).re := by
      by_cases he : n = -(K:ℤ)
      · rw [he]
      · exact le_trans (re_le_of_complexLexLE (hw _))
          (re_le_of_complexLexLE (hc _ n (by omega)))
    have hright : (η n).re ≤ (η (K:ℤ)).re := by
      by_cases he : n = (K:ℤ)
      · rw [he]
      · exact le_trans (re_le_of_complexLexLE (hc n _ (by omega)))
          (re_le_of_complexLexLE (hw _))
    have hmid := re_le_of_complexLexLE (hw n)
    constructor
    · change |(ξ n).re| < _
      rw [abs_lt]
      constructor <;> nlinarith [Real.pi_pos]
    · change |(η n).re| < _
      rw [abs_lt]
      constructor <;> nlinarith [Real.pi_pos]
  · intro n hn
    have hout (z : ℂ) (hz : |z.re-Real.pi*n| < Real.pi/4) : z ∉ rootCentralStrip K := by
      intro hmem
      change |z.re| < Real.pi*K+Real.pi/2 at hmem
      have hm := abs_lt.mp hmem
      have hb := abs_lt.mp hz
      by_cases hpos : 0 ≤ n
      · have hnk : (K:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast (show (K:ℤ)+1 ≤ n by omega)
        nlinarith [Real.pi_pos]
      · have hnk : (n:ℝ) ≤ -(K:ℝ)-1 := by exact_mod_cast (show n ≤ -(K:ℤ)-1 by omega)
        nlinarith [Real.pi_pos]
    exact ⟨hout _ (hxr n hn.le),hout _ (hyr n hn.le)⟩

/-- A strip separating central and tail indices recovers every central multiplicity from the global count. -/
theorem paired_central_count (ξ η : ℤ → ℂ) (K : ℕ)
    (hin : ∀ n : ℤ, n.natAbs ≤ K → ξ n ∈ rootCentralStrip K ∧ η n ∈ rootCentralStrip K)
    (hout : ∀ n : ℤ, K < n.natAbs → ξ n ∉ rootCentralStrip K ∧ η n ∉ rootCentralStrip K)
    (z : ℂ) :
    (∑ n ∈ Finset.Icc (-(K:ℤ)) K, ({ξ n,η n} : Multiset ℂ)).count z =
      if z ∈ rootCentralStrip K then ∑ᶠ n : ℤ, ({ξ n,η n} : Multiset ℂ).count z else 0 := by
  rw [Multiset.count_sum']
  by_cases hz : z ∈ rootCentralStrip K
  · rw [if_pos hz]
    symm
    apply finsum_eq_sum_of_support_subset
    intro n hn
    by_contra hnK
    have ht := hout n (by simp only [Finset.mem_coe,Finset.mem_Icc] at hnK; omega)
    have hc : ({ξ n,η n} : Multiset ℂ).count z = 0 := by
      apply Multiset.count_eq_zero.mpr
      simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton]
      rintro (rfl | rfl)
      · exact ht.1 hz
      · exact ht.2 hz
    exact hn hc
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro n hn
    have ht := hin n (by simp only [Finset.mem_Icc] at hn; omega)
    apply Multiset.count_eq_zero.mpr
    simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton]
    rintro (rfl | rfl)
    · exact hz ht.1
    · exact hz ht.2

/-- Ordered paired l2 perturbations with equal global multiplicities agree, including repeated entries. -/
theorem ordered_paired_unique_of_l2 (ξ η a b : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi:ℂ)*n) 2)
    (hη : Memℓp (fun n => η n-(Real.pi:ℂ)*n) 2)
    (ha : Memℓp (fun n => a n-(Real.pi:ℂ)*n) 2)
    (hb : Memℓp (fun n => b n-(Real.pi:ℂ)*n) 2)
    (hw : ∀ n, complexLexLE (ξ n) (η n))
    (hc : ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j))
    (hw' : ∀ n, complexLexLE (a n) (b n))
    (hc' : ∀ i j : ℤ, i < j → complexLexLE (b i) (a j))
    (hmult : ∀ z, (∑ᶠ n : ℤ, ({ξ n,η n} : Multiset ℂ).count z) =
      ∑ᶠ n : ℤ, ({a n,b n} : Multiset ℂ).count z) : ξ = a ∧ η = b := by
  obtain ⟨N₁,h₁⟩ := Coeff.exists_cutoff_norm_apply_lt (by simp)
    (⟨_,hξ⟩ : Coeff 2) (by positivity : 0 < Real.pi/4)
  obtain ⟨N₂,h₂⟩ := Coeff.exists_cutoff_norm_apply_lt (by simp)
    (⟨_,hη⟩ : Coeff 2) (by positivity : 0 < Real.pi/4)
  obtain ⟨N₃,h₃⟩ := Coeff.exists_cutoff_norm_apply_lt (by simp)
    (⟨_,ha⟩ : Coeff 2) (by positivity : 0 < Real.pi/4)
  obtain ⟨N₄,h₄⟩ := Coeff.exists_cutoff_norm_apply_lt (by simp)
    (⟨_,hb⟩ : Coeff 2) (by positivity : 0 < Real.pi/4)
  have he (n : ℤ) : ξ n = a n ∧ η n = b n := by
    let K := max (max N₁ N₂) (max N₃ N₄)+n.natAbs
    have hxy := ordered_pair_centralStrip ξ η K hw hc
      (fun k hk => h₁ k (by dsimp [K] at hk; omega))
      (fun k hk => h₂ k (by dsimp [K] at hk; omega))
    have hab := ordered_pair_centralStrip a b K hw' hc'
      (fun k hk => h₃ k (by dsimp [K] at hk; omega))
      (fun k hk => h₄ k (by dsimp [K] at hk; omega))
    have hcentral : (∑ k ∈ Finset.Icc (-(K:ℤ)) K, ({ξ k,η k} : Multiset ℂ)) =
        ∑ k ∈ Finset.Icc (-(K:ℤ)) K, ({a k,b k} : Multiset ℂ) := by
      apply Multiset.ext.mpr
      intro z
      rw [paired_central_count ξ η K hxy.1 hxy.2 z,
        paired_central_count a b K hab.1 hab.2 z,hmult z]
    apply ordered_paired_multiset_enumeration_unique complexLexLE
      (Finset.Icc (-(K:ℤ)) K) ξ η a b hcentral
      (fun k _ => hw k) (fun i _ j _ hij => hc i j hij)
      (fun k _ => hw' k) (fun i _ j _ hij => hc' i j hij) n
    simp only [Finset.mem_Icc]
    dsimp [K]
    omega
  exact ⟨funext (fun n => (he n).1),funext (fun n => (he n).2)⟩

end NLS
