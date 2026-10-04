import NLS.SequenceSpaces.RefinedTripleProduct
import NLS.SequenceSpaces.ReciprocalRowSumCoefficients
import NLS.ZakharovShabat.SourceSecondMomentFrequencyAnalytic

/-! # Refined sequence bounds for the actual frequency correction

The cubic gap weights control the sum of all off-diagonal moment rows.
The diagonal remainder is a product of two gaps and its actual diagonal
coefficient. Both belong to every finite lr with r > 1 and r >= p/3.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The exact frequency remainder, with its leading squared gap removed. -/
def SourceAbelianMomentAtlas.frequencyCorrection
    (A : SourceAbelianMomentAtlas hp hp1 W s) (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  A.renormalizedFrequency n ψ + (sourcePeriodicGapDisplacement hp hp1 ψ n)^2/2

/-- Refined norm bounds for the summed frequency correction, with no
exchange of two infinite sums and no uniform-tail assumption on the rows. -/
theorem SourceAbelianMomentAtlas.exists_refined_frequencyCorrection_coefficients
    (A : SourceAbelianMomentAtlas hp hp1 W s) (hr : r ≠ ⊤) (hr1 : 1 < r)
    (hpr : ENNReal.ofReal (p.toReal/3) ≤ r) (ψ : CoeffPair p)
    (d : Coeff p) (a : ℤ → Coeff p) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ ≤ R) (hd : ‖d‖ ≤ M)
    (ha : ∀ n, ‖a n‖ ≤ M)
    (hdiag : ∀ n, A.moment n n 2 ψ =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2/4*((Real.pi:ℂ)+d n))
    (hoff : ∀ n k, k ≠ n → A.moment n k 2 ψ =
      (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a n k) :
    ∃ b : Coeff r, (∀ n, b n = A.frequencyCorrection ψ n) ∧
      ‖b‖ ≤ ‖(4/(2*Real.pi):ℂ)‖ *
        (M*(R^3*‖Coeff.puncturedLattice (min r p.conjExponent)
          (lt_min hr1 ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))‖)+R^2*M/4) := by
  classical
  let g := sourcePeriodicGapDisplacement hp hp1 ψ
  obtain ⟨G,hG,hGn⟩ := Coeff.exists_refined_triple_product hp (zero_lt_one.trans hp1)
    hr (zero_lt_one.trans hr1) hpr g g g
  have hGnorm : ‖G‖ ≤ R^3 := by
    apply hGn.trans
    calc
      _ ≤ R*R*R := by gcongr
      _ = _ := by ring
  let u (n k : ℤ) : ℂ := if k = n then 0 else A.moment n k 2 ψ
  have hub (n k : ℤ) : ‖u n k‖ ≤ if k = n then 0 else ‖G k‖*‖a n k‖/|((n-k:ℤ):ℝ)| := by
    by_cases hk : k = n
    · simp [u,hk]
    · simp only [u,if_neg hk,hoff n k hk,hG k,norm_mul,norm_div,norm_pow,Complex.norm_intCast]
      change ‖g k‖^3 / |((n-k:ℤ):ℝ)| *‖a n k‖ ≤ ‖g k‖*‖g k‖*‖g k‖*‖a n k‖/|((n-k:ℤ):ℝ)|
      exact le_of_eq (by ring)
  obtain ⟨hsum,B,hB,hBn⟩ := Coeff.exists_reciprocal_rowSum_coefficients hp hp1 hr hr1 G a u M hM ha hub
  obtain ⟨H,hH,hHn⟩ := Coeff.exists_refined_triple_product hp (zero_lt_one.trans hp1)
    hr (zero_lt_one.trans hr1) hpr g g d
  have hHnorm : ‖H‖ ≤ R^2*M := by
    apply hHn.trans
    calc
      _ ≤ R*R*M := by gcongr
      _ = _ := by ring
  let b : Coeff r := -(4/(2*Real.pi):ℂ) • (B+(1/4:ℂ) • H)
  refine ⟨b,?_,?_⟩
  · intro n
    have hu : Summable (Function.update (fun k => A.moment n k 2 ψ) n 0) := by
      apply (hsum n).of_norm.congr
      intro k
      by_cases hk : k = n <;> simp [u,hk]
    have he := Summable.tsum_eq_add_tsum_ite' n hu
    change (∑' k, A.moment n k 2 ψ) = A.moment n n 2 ψ + ∑' k, u n k at he
    simp only [b,lp.coeFn_smul,Pi.smul_apply,lp.coeFn_add,Pi.add_apply,smul_eq_mul,hB n,hH n]
    unfold frequencyCorrection renormalizedFrequency
    rw [he,hdiag n]
    change _ = -(4/(2*Real.pi):ℂ)*(g n^2/4*((Real.pi:ℂ)+d n)+∑' k, u n k)+g n^2/2
    have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  · have hnorm : ‖b‖ ≤ ‖(4/(2*Real.pi):ℂ)‖*(‖B‖+‖H‖/4) := by
      rw [norm_smul,norm_neg]
      apply mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans_eq ?_) (norm_nonneg _)
      rw [norm_smul]
      norm_num
      ring
    apply hnorm.trans
    gcongr
    · exact hBn.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hGnorm (lp.norm_nonneg' _)) hM)

end NLS.ZakharovShabat
