import NLS.SequenceSpaces.DisjointCoefficientSums
import NLS.SequenceSpaces.SimultaneousBlockApproximation
import NLS.SequenceSpaces.BoundedCoefficientWeakLimit
import NLS.SequenceSpaces.StrictPowerGrowth

/-! # The block-growth contradiction in Pitt's theorem -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A bounded coefficient-null sequence cannot have images bounded away
from zero under an operator into a strictly smaller finite sequence exponent. -/
theorem not_lower_bound_image_of_bounded_coefficient_null
    (hp : p ≠ ⊤) (hqp : q < p) (T : Coeff p →L[ℂ] Coeff q)
    (x : ℕ → Coeff p) (hx : Bornology.IsBounded (range x))
    (hc : ∀ n, Tendsto (fun k => x k n) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ k, δ ≤ ‖T (x k)‖) : False := by
  classical
  have hq : q ≠ ⊤ := ne_top_of_le_ne_top hp hqp.le
  have hp1 : 1 < p := lt_of_le_of_lt (Fact.out : 1 ≤ q) hqp
  have hpR : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hqR : 0 < q.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
  have hqpR : q.toReal < p.toReal := (ENNReal.toReal_lt_toReal hq hp).mpr hqp
  obtain ⟨M,hM⟩ := hx.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg (x 0)).trans (hM _ ⟨0,rfl⟩)
  let ε (n : ℕ) : ℝ := δ/4*(1/2)^n
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ δ/4 := by
    dsimp [ε]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hsum (N : ℕ) : ∑ n ∈ Finset.range N, ε n ≤ δ/2 := by
    have he : ∑ n ∈ Finset.range N, ε n = δ/2*(1-(1/2 : ℝ)^N) := by
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ,ih]; dsimp [ε]; rw [pow_succ]; ring
    rw [he]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) N]
  obtain ⟨σ,_,S,hS,herr⟩ := exists_simultaneous_disjoint_blocks hp hq x (fun k => T (x k)) hc
    (tendsto_operator_coordinates_of_bounded_coefficient_null hp hp1 x hx hc T) ε hε
  let X (n : ℕ) := truncate (S n) (x (σ n))
  let Y (n : ℕ) := truncate (S n) (T (x (σ n)))
  have hsupp {r : ℝ≥0∞} (i : ℕ) (a : Coeff r) :
      Function.support (truncate (S i) a) ⊆ (S i : Set ℤ) := by
    intro n hn
    by_contra hni
    change n ∉ S i at hni
    exact hn (by simp [truncate_apply,hni])
  have hXd : Pairwise (fun i j => Disjoint (Function.support (X i)) (Function.support (X j))) := by
    intro i j hij
    exact (Finset.disjoint_coe.mpr (hS hij)).mono (hsupp i _) (hsupp j _)
  have hYd : Pairwise (fun i j => Disjoint (Function.support (Y i)) (Function.support (Y j))) := by
    intro i j hij
    exact (Finset.disjoint_coe.mpr (hS hij)).mono (hsupp i _) (hsupp j _)
  have hX (n : ℕ) : ‖X n‖ ≤ M :=
    (norm_truncate_le (zero_lt_one.trans hp1).ne' _ _).trans (hM _ ⟨σ n,rfl⟩)
  have hY (n : ℕ) : δ/2 ≤ ‖Y n‖ := by
    have he := (herr n).2
    have hnorm := norm_sub_norm_le (T (x (σ n))) (Y n)
    have hl := hlower (σ n)
    have hle := hεle n
    change ‖T (x (σ n))-Y n‖ < ε n at he
    linarith
  have herror (n : ℕ) : ‖T (X n)-Y n‖ ≤ (‖T‖+1)*ε n := by
    have he : T (X n)-Y n = T (X n-x (σ n))+(T (x (σ n))-Y n) := by rw [map_sub]; abel
    rw [he]
    apply (norm_add_le _ _).trans
    have hxerr : ‖X n-x (σ n)‖ ≤ ε n := by rw [norm_sub_rev]; exact (herr n).1.le
    have hyerr : ‖T (x (σ n))-Y n‖ ≤ ε n := (herr n).2.le
    calc
      _ ≤ ‖T‖*‖X n-x (σ n)‖+ε n := add_le_add (T.le_opNorm _) hyerr
      _ ≤ (‖T‖+1)*ε n := by nlinarith [norm_nonneg T]
  have herrorsum (N : ℕ) :
      ‖T (∑ n ∈ Finset.range N, X n)-∑ n ∈ Finset.range N, Y n‖ ≤ (‖T‖+1)*(δ/2) := by
    rw [map_sum,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖T (X n)-Y n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, (‖T‖+1)*ε n := Finset.sum_le_sum (fun n _ => herror n)
      _ = (‖T‖+1)*∑ n ∈ Finset.range N, ε n := by rw [Finset.mul_sum]
      _ ≤ (‖T‖+1)*(δ/2) := mul_le_mul_of_nonneg_left (hsum N) (by positivity)
  apply NLS.not_forall_nat_rpow_growth (C := ‖T‖*M) (one_div_pos.mpr hpR)
    (one_div_lt_one_div_of_lt hqR hqpR) (half_pos hδ)
    (show 0 ≤ (‖T‖+1)*(δ/2) by positivity)
  intro N
  have hinput := norm_sum_le_card_rpow_of_disjoint hpR (Finset.range N) X
    (fun i _ j _ hij => hXd hij) hM0 (fun i _ => hX i)
  have houtput := card_rpow_mul_le_norm_sum_of_disjoint hqR (Finset.range N) Y
    (fun i _ j _ hij => hYd hij) (by positivity : 0 ≤ δ/2) (fun i _ => hY i)
  simp only [Finset.card_range] at hinput houtput
  have hn := norm_sub_norm_le (∑ n ∈ Finset.range N, Y n) (T (∑ n ∈ Finset.range N, X n))
  rw [norm_sub_rev] at hn
  have hop := T.le_opNorm (∑ n ∈ Finset.range N, X n)
  have herrsum := herrorsum N
  nlinarith [norm_nonneg T]

end NLS.Coeff
