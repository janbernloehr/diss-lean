import NLS.SequenceSpaces.WeightedReciprocalKernel

/-! Two actual Holder rows control a whole negative-weight reciprocal
column. The sum splitting of the polynomial weight is essential; no
pointwise-to-sequence inference or logarithmic endpoint bound is used. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q r s : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [Fact (1 ≤ s)]

theorem weighted_reciprocal_columns_of_holder_rows
    (A σ : ℝ) (hσ : 0≤σ)
    (hpq : p.toReal.HolderConjugate q.toReal) (hrs : r.toReal.HolderConjugate s.toReal)
    (a₁ : Coeff p) (b₁ : Coeff q) (a₂ : Coeff r) (b₂ : Coeff s)
    (ha₁ : ∀ n : ℤ, ‖a₁ n‖=Weight.sobolev σ n*Weight.sobolev (-A) n)
    (hb₁ : ∀ n : ℤ, ‖b₁ n‖=‖puncturedLattice 2 (by norm_num) n‖)
    (ha₂ : ∀ n : ℤ, ‖a₂ n‖=Weight.sobolev (-A) n)
    (hb₂ : ∀ n : ℤ, ‖b₂ n‖=Weight.sobolev σ n*‖puncturedLattice 2 (by norm_num) n‖) :
    ∃ C : ℝ, 0≤C ∧ ∀ k : ℤ,
      Summable (fun n : ℤ => Weight.sobolev (-A) n*‖puncturedLattice 2 (by norm_num) (n-k)‖) ∧
      Weight.sobolev σ k*(∑' n : ℤ, Weight.sobolev (-A) n*‖puncturedLattice 2 (by norm_num) (n-k)‖)≤C := by
  let L := (2 : ℝ)^σ
  let C := L*(‖a₁‖*‖b₁‖+‖a₂‖*‖b₂‖)
  have hL : 0≤L := by dsimp only [L];positivity
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro k
  obtain ⟨h₁,hb₁norm⟩ := holder_absolute_row hpq a₁ b₁ k
  obtain ⟨h₂,hb₂norm⟩ := holder_absolute_row hrs a₂ b₂ k
  let f := fun n : ℤ => Weight.sobolev (-A) n*‖puncturedLattice 2 (by norm_num) (n-k)‖
  let H := fun n : ℤ => L*(‖a₁ n‖*‖b₁ (k-n)‖+‖a₂ n‖*‖b₂ (k-n)‖)
  have hH : Summable H := (h₁.add h₂).mul_left L
  have hf (n : ℤ) : 0≤f n := mul_nonneg ((Weight.sobolev (-A)).positive n).le (norm_nonneg _)
  have hpoint (n : ℤ) : Weight.sobolev σ k*f n≤H n := by
    have hn : n-k=-(k-n) := by omega
    dsimp only [f,H]
    rw [hn,norm_puncturedLattice_neg,ha₁,hb₁,ha₂,hb₂]
    calc
      _≤(L*(Weight.sobolev σ n+Weight.sobolev σ (k-n)))*
          (Weight.sobolev (-A) n*‖puncturedLattice 2 (by norm_num) (k-n)‖) :=
        mul_le_mul_of_nonneg_right (Weight.sobolev_sum_bound σ hσ n k)
          (mul_nonneg ((Weight.sobolev (-A)).positive n).le (norm_nonneg _))
      _=_ := by ring
  have hs := hH.of_nonneg_of_le (fun n => mul_nonneg ((Weight.sobolev σ).positive k).le (hf n)) hpoint
  have hfs : Summable f := by
    have h := hs.mul_left (Weight.sobolev σ k)⁻¹
    simpa only [←mul_assoc,inv_mul_cancel₀ ((Weight.sobolev σ).positive k).ne',one_mul] using h
  refine ⟨hfs,?_⟩
  have hb := hs.tsum_le_tsum hpoint hH
  rw [tsum_mul_left,tsum_mul_left,h₁.tsum_add h₂] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add hb₁norm hb₂norm) hL)

end NLS.Coeff
