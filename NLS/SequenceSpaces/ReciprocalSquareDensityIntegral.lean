import NLS.SequenceSpaces.WeightedReciprocalSquareDecay
import Mathlib.MeasureTheory.Integral.Prod

/-! # Weighted reciprocal-square density integrals

An l1 bound on the squared-bracket-weighted masses gives joint integrability
and inverse-square-bracket decay of the full punctured index-angle integral.
The statement includes index zero and requires no finite-support hypothesis.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.Coeff

/-- A weighted l1 mass majorant controls the full index-angle reciprocal-square integral. -/
theorem reciprocal_square_density_integral_bound (a : Coeff 1) (d : ℤ → ℝ → ℝ)
    (hdm : ∀ m, Measurable (d m)) (hdi : ∀ m, Integrable (d m))
    (hdn : ∀ m θ, 0 ≤ d m θ)
    (hdmass : ∀ m : ℤ, (∫ θ : ℝ, d m θ) ≤ ‖a m‖/(1+|(m:ℝ)|)^2) (n : ℤ) :
    Integrable (fun z : {m : ℤ // m ≠ n} × ℝ => d z.1.val z.2/|((n-z.1.val:ℤ):ℝ)|^2)
      (Measure.count.prod volume) ∧
    (1+|(n:ℝ)|)^2*(∫ z : {m : ℤ // m ≠ n} × ℝ,
      d z.1.val z.2/|((n-z.1.val:ℤ):ℝ)|^2 ∂(Measure.count.prod volume)) ≤ 4*‖a‖ := by
  let b : ℤ → ℝ := fun m => ‖a m‖/(1+|(m:ℝ)|)^2*‖shift n (puncturedLattice 2 (by norm_num)) m‖^2
  have hbn (m : ℤ) : 0 ≤ b m := by dsimp [b]; positivity
  have hu (m : ℤ) : ‖(b m:ℂ)‖ ≤ 1*‖a m‖/(1+|(m:ℝ)|)^2*
      ‖shift n (puncturedLattice 2 (by norm_num)) m‖^2 := by
    rw [Complex.norm_real,Real.norm_of_nonneg (hbn m),one_mul]
  obtain ⟨hs,hb⟩ := summable_norm_reciprocal_sq_of_weighted_l1 a (fun m => (b m:ℂ)) n 1 (by norm_num) hu
  simp only [Complex.norm_real,Real.norm_of_nonneg (hbn _),mul_one] at hs hb
  have he (m : {m : ℤ // m ≠ n}) : b m.val = ‖a m.val‖/(1+|(m.val:ℝ)|)^2/|((n-m.val:ℤ):ℝ)|^2 := by
    dsimp only [b]
    rw [norm_shift_puncturedLattice_apply,if_neg m.property]
    rw [Int.cast_sub,abs_sub_comm,inv_pow]
    simp only [Int.cast_sub,div_eq_mul_inv]
  let f := fun z : {m : ℤ // m ≠ n} × ℝ => d z.1.val z.2/|((n-z.1.val:ℤ):ℝ)|^2
  have hfn (z) : 0 ≤ f z := div_nonneg (hdn _ _) (sq_nonneg _)
  have hfm : Measurable f := by
    apply measurable_from_prod_countable_right
    intro m
    exact (hdm m.val).div_const (|((n-m.val:ℤ):ℝ)|^2)
  have hfi (m : {m : ℤ // m ≠ n}) : Integrable (fun θ => f (m,θ)) := (hdi m.val).div_const (|((n-m.val:ℤ):ℝ)|^2)
  have hmass (m : {m : ℤ // m ≠ n}) : (∫ θ : ℝ, ‖f (m,θ)‖) ≤ b m.val := by
    simp only [Real.norm_of_nonneg (hfn _)]
    dsimp [f]
    rw [integral_div,he m]
    exact div_le_div_of_nonneg_right (hdmass m.val) (sq_nonneg _)
  have hmassS : Summable (fun m : {m : ℤ // m ≠ n} => ∫ θ : ℝ, ‖f (m,θ)‖) :=
    (hs.subtype (fun m => m ≠ n)).of_nonneg_of_le (fun m => integral_nonneg (fun θ => norm_nonneg _)) hmass
  have hi : Integrable f (Measure.count.prod volume) := by
    apply (integrable_prod_iff hfm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hfi,integrable_count_iff.mpr ?_⟩
    simpa only [Real.norm_of_nonneg (integral_nonneg (fun θ => norm_nonneg (f (_,θ))))] using hmassS
  refine ⟨hi,?_⟩
  change (1+|(n:ℝ)|)^2*(∫ z, f z ∂(Measure.count.prod volume)) ≤ _
  rw [integral_prod _ hi,integral_countable hi.integral_prod_left]
  simp only [measureReal_def,Measure.count_singleton,ENNReal.toReal_one,one_smul]
  have hsub : (∑' m : {m : ℤ // m ≠ n}, ∫ θ : ℝ, f (m,θ)) ≤ ∑' m : ℤ, b m := by
    have h := hmassS.tsum_le_tsum hmass (hs.subtype (fun m => m ≠ n))
    simp only [Real.norm_of_nonneg (hfn _)] at h
    exact h.trans (hs.tsum_subtype_le b {m | m ≠ n} hbn)
  exact (mul_le_mul_of_nonneg_left hsub (sq_nonneg _)).trans hb

end NLS.Coeff
