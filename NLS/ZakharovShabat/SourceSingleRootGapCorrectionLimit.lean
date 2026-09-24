import NLS.ZakharovShabat.SourceMidpointProductCutoffLimit
import NLS.ZakharovShabat.SourceSingleRootQuotientTailLimit

/-!
# The infinite squared-gap correction in Lemma 10.8

The finite quotient-minus-midpoint estimate passes to the analytic
infinite quotient and the unconditional midpoint product. A small
reciprocal-square row gives a bound linear in that row, rather than
only a uniform exponential bound.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- On a small squared-gap row, every finite quotient differs from its
midpoint factor by at most a fixed numerator exponential times that row. -/
theorem norm_sourceSingleRootQuotientPartialProduct_sub_midpoint_le_of_small_row
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ ψ : CoeffPair p) (a : Coeff p) (α : Coeff q)
    (hα : ∀ m : ℤ,
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m)
    (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-z‖)
    (n : ℤ) (M : ℕ) (z : ℂ)
    (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (hrowSmall : (C^2/4)*
      (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤ 1/2) :
    ‖sourceSingleRootQuotientPartialProduct hp hp1 n M (z,(a,ψ)) -
      sourceSingleRootMidpointPartialProduct hp hp1 n M (z,(a,ψ))‖ ≤
      Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖) *
        C^2*(∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) := by
  let s : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase n
  let P := sourceSingleRootMidpointPartialProduct hp hp1 n M (z,(a,ψ))
  let A := C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖
  let T := ∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m
  let B := (C^2/2)*T
  let D := 2*∑ m ∈ s, ‖sourceSingleRootGapRadicand hp hp1 ψ m z‖
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact tsum_nonneg (fun m => by
      unfold sourceSquaredGapReciprocalTerm
      split_ifs <;> positivity)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : B ≤ 1 := by dsimp [B,T]; nlinarith [hrowSmall]
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDB : D ≤ B := by
    have hrow := sourceSingleRootGapRadicand_sum_le_reciprocal_row
      hp hp1 φ ψ N ε C hC hsep n z hz s
        (fun m hm => Finset.ne_of_mem_erase hm)
    dsimp [D,B,T]
    nlinarith
  have hsmall (m : ℤ) (hm : m ∈ s) :
      ‖sourceSingleRootGapRadicand hp hp1 ψ m z‖ ≤ 1/2 :=
    sourceSingleRootGapRadicand_le_half_of_row_bound
      hp hp1 φ ψ N ε C hC hsep n m
        (Ne.symm (Finset.ne_of_mem_erase hm)) z hz hrowSmall
  have hP1 : ‖P-1‖ ≤ Real.exp A-1 :=
    norm_sourceSingleRootMidpointPartialProduct_sub_one_le
      hp hp1 hq φ ψ a α hα N ε C hC hsep n M z hz
  have hP : ‖P‖ ≤ Real.exp A := by
    calc
      ‖P‖ = ‖(P-1)+1‖ := by simp
      _ ≤ ‖P-1‖+‖(1:ℂ)‖ := norm_add_le _ _
      _ ≤ Real.exp A := by norm_num; linarith
  have hDexp : 0 ≤ Real.exp D-1 := by
    have := Real.add_one_le_exp D
    linarith
  have hBexp : Real.exp B-1 ≤ 2*B := by
    have h := Real.abs_exp_sub_one_le (x := B)
      (by simpa only [abs_of_nonneg hB0] using hB1)
    exact (le_abs_self _).trans (by simpa only [abs_of_nonneg hB0] using h)
  have hfinite := norm_sourceSingleRootQuotientPartialProduct_sub_midpoint_le
    hp hp1 n M (z,(a,ψ)) hsmall
  calc
    _ ≤ ‖P‖*(Real.exp D-1) := by simpa only [P,D,s] using hfinite
    _ ≤ Real.exp A*(Real.exp D-1) := mul_le_mul_of_nonneg_right hP hDexp
    _ ≤ Real.exp A*(Real.exp B-1) :=
      mul_le_mul_of_nonneg_left
        (sub_le_sub_right (Real.exp_le_exp.mpr hDB) 1) (Real.exp_nonneg _)
    _ ≤ Real.exp A*(2*B) :=
      mul_le_mul_of_nonneg_left hBexp (Real.exp_nonneg _)
    _ = Real.exp A*C^2*T := by dsimp [B]; ring

/-- The actual analytic infinite quotient differs from the infinite
midpoint product by a quantity linear in the squared-gap row. -/
theorem norm_sourceSingleRootQuotientJointProduct_sub_midpoint_le_of_small_row
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ ψ : CoeffPair p) (a : Coeff p) (α : Coeff q)
    (hα : ∀ m : ℤ,
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m)
    (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-z‖)
    (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (hdom : (z,(a,ψ)) ∈ sourceSingleRootQuotientJointDomain hp hp1 Set.univ n)
    (hrowSmall : (C^2/4)*
      (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤ 1/2) :
    ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)) -
      (sourceMidpointProductRow hp hp1 ψ α n z+1)‖ ≤
      Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖) *
        C^2*(∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) := by
  have hQ := tendsto_sourceSingleRootQuotientPartialProduct
    hp hp1 n Set.univ (z,(a,ψ)) hdom
  have hP := tendsto_sourceSingleRootMidpointPartialProduct
    hq hp hp1 φ ψ N ε C hC hsep a α hα n z hz
  apply le_of_tendsto ((hQ.sub hP).norm)
  exact Filter.Eventually.of_forall fun M =>
    norm_sourceSingleRootQuotientPartialProduct_sub_midpoint_le_of_small_row
      hp hp1 hq φ ψ a α hα N ε C hC hsep n M z hz hrowSmall

end NLS.ZakharovShabat
