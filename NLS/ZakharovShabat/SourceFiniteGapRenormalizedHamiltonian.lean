import NLS.ZakharovShabat.SourcePrimitivePowerHamiltonian
import NLS.ZakharovShabat.SourcePrimitivePowerPositive

/-! # The sign of the finite-gap renormalized Hamiltonian

The physical correction is real and nonpositive. It is strictly negative
whenever any spectral gap is open, and vanishes exactly when all gaps close.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The physical finite-gap quantity to be extended in Theorem 18.3. -/
def sourceFiniteGapRenormalizedHamiltonian (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) : ℂ :=
  sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2-
    (∑' n : ℤ, (2*(n:ℂ)*Real.pi)^2*sourceComplexAction hp hp1 n φ.val)

namespace SourcePrimitivePowerAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- Lemma 21.2 as a finite sum of nonnegative real cubic moments. -/
theorem finiteGap_renormalizedHamiltonian_eq_real_sum (φ : realTypeSourceLocus p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapRenormalizedHamiltonian hp hp1 φ hf =
      ((-(4/3:ℝ)*(∑ n ∈ hf.toFinset, (A.moment n 3 φ.val).re) : ℝ) : ℂ) := by
  classical
  rw [sourceFiniteGapRenormalizedHamiltonian,A.finiteGap_hamiltonian_identity φ hf]
  have hsum : (∑' n : ℤ, A.moment n 3 φ.val) = ∑ n ∈ hf.toFinset, A.moment n 3 φ.val := by
    apply tsum_eq_sum
    intro n hn
    apply A.moment_of_collapsed φ.val (A.realType_subset_domain φ.property) n
    by_contra hne
    exact hn (hf.mem_toFinset.mpr hne)
  rw [hsum]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  apply Complex.ext
  · rfl
  · simpa only [ofReal_im] using A.real_odd_moment_im φ n 1

end SourcePrimitivePowerAtlas

/-- The finite-gap physical correction is real and nonpositive. -/
theorem sourceFiniteGapRenormalizedHamiltonian_nonpos (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    (sourceFiniteGapRenormalizedHamiltonian hp hp1 φ hf).re ≤ 0 ∧
      (sourceFiniteGapRenormalizedHamiltonian hp hp1 φ hf).im = 0 := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas hp hp1
  rw [A.finiteGap_renormalizedHamiltonian_eq_real_sum φ hf]
  simp only [ofReal_re,ofReal_im,and_true]
  have hpos : 0 ≤ ∑ n ∈ hf.toFinset, (A.moment n 3 φ.val).re :=
    Finset.sum_nonneg (fun n _ => (A.real_moment_nonneg φ n 3).1)
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hpos

/-- Any open gap makes the physical correction strictly negative. -/
theorem sourceFiniteGapRenormalizedHamiltonian_neg_of_open_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    (sourceFiniteGapRenormalizedHamiltonian hp hp1 φ hf).re < 0 := by
  classical
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas hp hp1
  rw [A.finiteGap_renormalizedHamiltonian_eq_real_sum φ hf,ofReal_re]
  have hle : (A.moment n 3 φ.val).re ≤ ∑ k ∈ hf.toFinset, (A.moment k 3 φ.val).re :=
    Finset.single_le_sum (fun k _ => (A.real_moment_nonneg φ k 3).1) (hf.mem_toFinset.mpr hn)
  exact mul_neg_of_neg_of_pos (by norm_num) ((A.real_odd_moment_pos φ n 1 hn).trans_le hle)

/-- Vanishing of the correction is equivalent to closure of every gap. -/
theorem sourceFiniteGapRenormalizedHamiltonian_eq_zero_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapRenormalizedHamiltonian hp hp1 φ hf = 0 ↔
      ∀ n, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
  constructor
  · intro hzero n
    by_contra hn
    have hneg := sourceFiniteGapRenormalizedHamiltonian_neg_of_open_gap hp hp1 φ hf n hn
    simp only [hzero,zero_re,lt_self_iff_false] at hneg
  · intro hclosed
    obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas hp hp1
    rw [sourceFiniteGapRenormalizedHamiltonian,A.finiteGap_hamiltonian_identity φ hf]
    have hz (n : ℤ) : A.moment n 3 φ.val = 0 :=
      A.moment_of_collapsed φ.val (A.realType_subset_domain φ.property) n (hclosed n) 3
    simp only [hz,tsum_zero,mul_zero]

end NLS.ZakharovShabat
