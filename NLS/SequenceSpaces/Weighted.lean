import NLS.SequenceSpaces.Truncation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weighted Fourier coefficient spaces

A positive real weight gives a sequence space whose norm is the `lp` norm after
multiplication by the weight. This is a genuine subtype of raw coefficients;
the weighting equivalence transports the Banach-space structure from `lp`.
-/

open scoped ENNReal
noncomputable section

namespace NLS

/-- A strictly positive real weight on Fourier frequencies. -/
structure Weight where
  value : ℤ → ℝ
  positive : ∀ n, 0 < value n

instance : CoeFun Weight (fun _ => ℤ → ℝ) := ⟨Weight.value⟩

namespace Weight

theorem complex_ne_zero (w : Weight) (n : ℤ) : (w n : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (w.positive n))

/-- The unit weight recovers the unweighted space. -/
def one : Weight := ⟨fun _ => 1, fun _ => zero_lt_one⟩

/-- The Sobolev weight `(1 + |n|)^s`, for any real regularity `s`. -/
noncomputable def sobolev (s : ℝ) : Weight :=
  ⟨fun n => (1 + |(n : ℝ)|) ^ s,
    fun n => Real.rpow_pos_of_pos (by positivity) s⟩

@[simp]
theorem one_apply (n : ℤ) : one n = 1 := rfl

@[simp]
theorem sobolev_apply (s : ℝ) (n : ℤ) : sobolev s n = (1 + |(n : ℝ)|) ^ s := rfl

@[simp]
theorem sobolev_zero_apply (n : ℤ) : sobolev 0 n = 1 := by simp

end Weight

/-- Raw coefficients for which multiplication by `w` is in `lp`. -/
def weightedSubmodule (w : Weight) (p : ℝ≥0∞) : Submodule ℂ (ℤ → ℂ) where
  carrier := {a | Memℓp (fun n => (w n : ℂ) * a n) p}
  zero_mem' := by
    change Memℓp (fun n : ℤ => (w n : ℂ) * 0) p
    convert (zero_memℓp (E := fun _ : ℤ => ℂ) (p := p)) using 1
    funext n
    exact mul_zero _
  add_mem' := by
    intro a b ha hb
    change Memℓp (fun n => (w n : ℂ) * (a n + b n)) p
    change Memℓp (fun n => (w n : ℂ) * a n) p at ha
    change Memℓp (fun n => (w n : ℂ) * b n) p at hb
    convert ha.add hb using 1
    funext n
    exact mul_add _ _ _
  smul_mem' := by
    intro c a ha
    change Memℓp (fun n => (w n : ℂ) * (c * a n)) p
    change Memℓp (fun n => (w n : ℂ) * a n) p at ha
    simpa only [mul_left_comm] using ha.const_mul c

/-- Weighted complex Fourier coefficients, with their actual unweighted values. -/
def WeightedCoeff (w : Weight) (p : ℝ≥0∞) := ↥(weightedSubmodule w p)

namespace WeightedCoeff

variable (w : Weight) (p : ℝ≥0∞)

instance : AddCommGroup (WeightedCoeff w p) :=
  inferInstanceAs (AddCommGroup ↥(weightedSubmodule w p))

instance : Module ℂ (WeightedCoeff w p) :=
  inferInstanceAs (Module ℂ ↥(weightedSubmodule w p))

/-- Multiplying coefficients by the weight is an algebraic linear equivalence. -/
noncomputable def weightEquiv : WeightedCoeff w p ≃ₗ[ℂ] Coeff p where
  toFun a := ⟨fun n => (w n : ℂ) * a.val n, a.property⟩
  invFun a := ⟨fun n => a n / (w n : ℂ), by
    change Memℓp (fun n => (w n : ℂ) * (a n / (w n : ℂ))) p
    convert lp.memℓp a using 1
    funext n
    simp [div_eq_mul_inv, mul_comm, w.complex_ne_zero]⟩
  left_inv a := by
    apply Subtype.ext
    funext n
    simp [w.complex_ne_zero]
  right_inv a := by
    ext n
    simp [div_eq_mul_inv, mul_comm, w.complex_ne_zero]
  map_add' a b := by
    ext n
    exact mul_add _ _ _
  map_smul' c a := by
    ext n
    exact mul_left_comm _ _ _

noncomputable instance [Fact (1 ≤ p)] : NormedAddCommGroup (WeightedCoeff w p) :=
  NormedAddCommGroup.induced _ _ (weightEquiv w p).toLinearMap (weightEquiv w p).injective

noncomputable instance [Fact (1 ≤ p)] : NormedSpace ℂ (WeightedCoeff w p) :=
  NormedSpace.induced ℂ _ _ (weightEquiv w p).toLinearMap

/-- The weighted norm is chosen so that weighting is an isometry. -/
noncomputable def weightIsometry [Fact (1 ≤ p)] : WeightedCoeff w p ≃ₗᵢ[ℂ] Coeff p where
  toLinearEquiv := weightEquiv w p
  norm_map' _ := rfl

instance [Fact (1 ≤ p)] : CompleteSpace (WeightedCoeff w p) :=
  (weightIsometry w p).toIsometryEquiv.completeSpace

@[simp]
theorem weightEquiv_apply (a : WeightedCoeff w p) (n : ℤ) :
    weightEquiv w p a n = (w n : ℂ) * a.val n := rfl

/-- The weighted norm is exactly the `lp` norm of the weighted coefficients. -/
theorem norm_eq [Fact (1 ≤ p)] (a : WeightedCoeff w p) :
    ‖a‖ = ‖weightEquiv w p a‖ := rfl

/-- Individual Fourier coefficients obey the inverse-weight decay bound. -/
theorem norm_apply_le [Fact (1 ≤ p)] (a : WeightedCoeff w p) (n : ℤ) :
    ‖a.val n‖ ≤ ‖a‖ / w n := by
  apply (le_div_iff₀ (w.positive n)).mpr
  have h := lp.norm_apply_le_norm
    (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) (weightEquiv w p a) n
  simpa only [weightEquiv_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (w.positive n), mul_comm, norm_eq] using h

/-- Finite truncation transported through the weighting equivalence. -/
noncomputable def truncate (s : Finset ℤ) (a : WeightedCoeff w p) : WeightedCoeff w p :=
  (weightEquiv w p).symm (Coeff.truncate s (weightEquiv w p a))

@[simp]
theorem truncate_apply (s : Finset ℤ) (a : WeightedCoeff w p) (n : ℤ) :
    (truncate w p s a).val n = if n ∈ s then a.val n else 0 := by
  change Coeff.truncate s (weightEquiv w p a) n / (w n : ℂ) = _
  by_cases hn : n ∈ s <;> simp [hn, w.complex_ne_zero]

theorem norm_truncate_le [Fact (1 ≤ p)] (s : Finset ℤ) (a : WeightedCoeff w p) :
    ‖truncate w p s a‖ ≤ ‖a‖ := by
  rw [norm_eq, truncate, LinearEquiv.apply_symm_apply, norm_eq]
  exact Coeff.norm_truncate_le (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) s _

/-- Weighted truncations converge for every finite Banach exponent. -/
theorem tendsto_truncate [Fact (1 ≤ p)] (hp : p ≠ ⊤) (a : WeightedCoeff w p) :
    Filter.Tendsto (fun s : Finset ℤ => truncate w p s a) Filter.atTop (nhds a) := by
  have h := ((weightIsometry w p).symm.continuous.tendsto (weightEquiv w p a)).comp
    (Coeff.tendsto_truncate hp (weightEquiv w p a))
  change Filter.Tendsto
    (fun s => (weightEquiv w p).symm (Coeff.truncate s (weightEquiv w p a))) _
    (nhds ((weightEquiv w p).symm (weightEquiv w p a))) at h
  simpa only [truncate, LinearEquiv.symm_apply_apply] using h

end WeightedCoeff
end NLS
