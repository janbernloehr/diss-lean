import NLS.SequenceSpaces.SandwichMajorant
import NLS.FunctionalAnalysis.NeumannVectorSeries

/-! A single positive summable Neumann envelope dominates every bounded
coefficient-space correction compatible with the same positive operator. -/
noncomputable section
open scoped ENNReal
open NLS.FunctionalAnalysis
namespace NLS.Coeff

def IsNonnegative {p : ℝ≥0∞} (a : Coeff p) : Prop := ∀ k, a k = (‖a k‖:ℂ)

theorem isNonnegative_magnitude {p : ℝ≥0∞} (a : Coeff p) : IsNonnegative (magnitude a) := by
  intro k
  simp only [magnitude_apply, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]

theorem magnitude_eq_of_isNonnegative {p : ℝ≥0∞} (a : Coeff p) (ha : IsNonnegative a) :
    magnitude a = a := by
  ext k
  exact (ha k).symm

theorem isNonnegative_operator_power (S : Coeff 1 →L[ℂ] Coeff 1)
    (hS : ∀ v, IsNonnegative v → IsNonnegative (S v)) (a : Coeff 1) (ha : IsNonnegative a)
    (m : ℕ) : IsNonnegative ((S^m) a) := by
  induction m with
  | zero => simpa only [pow_zero, one_apply_eq_self] using ha
  | succ m ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact hS _ ih

theorem norm_neumannVectorSeries_apply_of_nonnegative
    (S : Coeff 1 →L[ℂ] Coeff 1) (hSn : ‖S‖ ≤ 1/2)
    (hS : ∀ v, IsNonnegative v → IsNonnegative (S v)) (a : Coeff 1) (ha : IsNonnegative a)
    (k : ℤ) :
    ‖neumannVectorSeries S a k‖ = ∑' m : ℕ, ‖(S^m) a k‖ := by
  have hs := (summable_norm_neumann_power_apply S hSn a).of_norm
  have he : neumannVectorSeries S a k = ∑' m : ℕ, (S^m) a k :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 k).map_tsum hs
  rw [he]
  have hp (m : ℕ) : (S^m) a k = (‖(S^m) a k‖:ℂ) :=
    isNonnegative_operator_power S hS a ha m k
  have hsum : (∑' m : ℕ, (S^m) a k) = ∑' m : ℕ, (‖(S^m) a k‖:ℂ) := tsum_congr hp
  rw [hsum, ← Complex.ofReal_tsum, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]

theorem summable_norm_neumann_coordinate {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : Coeff p →L[ℂ] Coeff p) (hT : ‖T‖ ≤ 1/2) (b : Coeff p) (k : ℤ) :
    Summable (fun m : ℕ => ‖(T^m) b k‖) :=
  (summable_norm_neumann_power_apply T hT b).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => lp.norm_apply_le_norm (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) ((T^m) b) k)

theorem neumannVectorSeries_apply_dominated
    (S : Coeff 1 →L[ℂ] Coeff 1) (hSn : ‖S‖ ≤ 1/2)
    (hS : ∀ v, IsNonnegative v → IsNonnegative (S v)) (a : Coeff 1) (ha : IsNonnegative a)
    (T : Coeff ⊤ →L[ℂ] Coeff ⊤) (hT : ‖T‖ ≤ 1/2) (b : Coeff ⊤)
    (hb : ∀ k, ‖b k‖ ≤ ‖a k‖)
    (hdom : ∀ (f : Coeff ⊤) (v : Coeff 1), IsNonnegative v →
      (∀ k, ‖f k‖ ≤ ‖v k‖) → ∀ k, ‖T f k‖ ≤ ‖S v k‖) (k : ℤ) :
    ‖neumannVectorSeries T b k‖ ≤ ‖neumannVectorSeries S a k‖ := by
  have hp (m : ℕ) : ∀ k, ‖(T^m) b k‖ ≤ ‖(S^m) a k‖ := by
    induction m with
    | zero => simpa only [pow_zero, one_apply_eq_self] using hb
    | succ m ih =>
      simp only [pow_succ', mul_apply_eq_comp]
      exact hdom _ _ (isNonnegative_operator_power S hS a ha m) ih
  have hs := (summable_norm_neumann_power_apply T hT b).of_norm
  have he : neumannVectorSeries T b k = ∑' m : ℕ, (T^m) b k :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ k).map_tsum hs
  rw [he, norm_neumannVectorSeries_apply_of_nonnegative S hSn hS a ha k]
  exact (norm_tsum_le_tsum_norm (summable_norm_neumann_coordinate T hT b k)).trans
    ((summable_norm_neumann_coordinate T hT b k).tsum_le_tsum (fun m => hp m k)
      (summable_norm_neumann_coordinate S hSn a k))

theorem exists_uniform_neumann_summable_majorant
    (S : Coeff 1 →L[ℂ] Coeff 1) (hSn : ‖S‖ ≤ 1/2)
    (hS : ∀ v, IsNonnegative v → IsNonnegative (S v)) (a : Coeff 1) (ha : IsNonnegative a) :
    ∃ H : Coeff 1, ‖H‖ ≤ 2*‖a‖ ∧
      ∀ (T : Coeff ⊤ →L[ℂ] Coeff ⊤) (b g : Coeff ⊤), ‖T‖ ≤ 1/2 →
        (∀ k, ‖b k‖ ≤ ‖a k‖) →
        (∀ (f : Coeff ⊤) (v : Coeff 1), IsNonnegative v →
          (∀ k, ‖f k‖ ≤ ‖v k‖) → ∀ k, ‖T f k‖ ≤ ‖S v k‖) →
        g-T g=b → ∀ k, ‖g k‖ ≤ ‖H k‖ := by
  refine ⟨neumannVectorSeries S a,norm_neumannVectorSeries_le_two S hSn a,?_⟩
  intro T b g hT hb hd hg k
  rw [eq_neumannVectorSeries_of_sub_eq T hT b g hg]
  exact neumannVectorSeries_apply_dominated S hSn hS a ha T hT b hb hd k

end NLS.Coeff
