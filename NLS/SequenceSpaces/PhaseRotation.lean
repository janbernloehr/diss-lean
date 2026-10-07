import NLS.SequenceSpaces.UniformTailContinuity
import Mathlib.Analysis.Complex.Trigonometric

/-! # Simultaneous phase rotations in sequence spaces

An arbitrary real angle sequence acts isometrically. At finite exponents,
pointwise continuous angles and norm-continuous amplitudes give a continuous
sequence-valued map. No uniform bound on the angles or frequencies is needed.
-/
noncomputable section
open Set Filter Topology Complex Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Multiply each coefficient by its own unit complex phase. -/
def phaseMultiply (θ : ℤ → ℝ) (a : Coeff p) : Coeff p :=
  ⟨fun n => Complex.exp ((θ n : ℂ)*I)*a n, by
    apply a.property.mono'
    intro n
    simp only [norm_mul, norm_exp_ofReal_mul_I, one_mul, le_refl]⟩

omit [Fact (1 ≤ p)] in
@[simp] theorem phaseMultiply_apply (θ : ℤ → ℝ) (a : Coeff p) (n : ℤ) :
    phaseMultiply θ a n = Complex.exp ((θ n : ℂ)*I)*a n := rfl

omit [Fact (1 ≤ p)] in
@[simp] theorem norm_phaseMultiply_apply (θ : ℤ → ℝ) (a : Coeff p) (n : ℤ) :
    ‖phaseMultiply θ a n‖ = ‖a n‖ := by simp

@[simp] theorem norm_phaseMultiply (θ : ℤ → ℝ) (a : Coeff p) : ‖phaseMultiply θ a‖ = ‖a‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  exact le_antisymm (lp.norm_mono hp (by intro n; simp)) (lp.norm_mono hp (by intro n; simp))

/-- Phase multiplication is a complex linear isometry, even for an unbounded angle sequence. -/
def phaseMultiplyLI (θ : ℤ → ℝ) : Coeff p →ₗᵢ[ℂ] Coeff p where
  toFun := phaseMultiply θ
  map_add' a b := by ext n; simp only [phaseMultiply_apply, lp.coeFn_add, Pi.add_apply]; ring
  map_smul' c a := by ext n; simp only [phaseMultiply_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  norm_map' := norm_phaseMultiply θ

omit [Fact (1 ≤ p)] in
@[simp] theorem phaseMultiply_zero_angles (a : Coeff p) : phaseMultiply (fun _ => 0) a = a := by
  ext n
  simp

omit [Fact (1 ≤ p)] in
/-- Independent phase rotations add their angle sequences. -/
theorem phaseMultiply_add_angles (θ η : ℤ → ℝ) (a : Coeff p) :
    phaseMultiply θ (phaseMultiply η a) = phaseMultiply (fun n => θ n+η n) a := by
  ext n
  simp only [phaseMultiply_apply, ofReal_add, add_mul, Complex.exp_add]
  ring

omit [Fact (1 ≤ p)] in
/-- Finite truncation commutes exactly with every phase rotation. -/
theorem truncate_phaseMultiply (s : Finset ℤ) (θ : ℤ → ℝ) (a : Coeff p) :
    truncate s (phaseMultiply θ a) = phaseMultiply θ (truncate s a) := by
  ext n
  by_cases hn : n ∈ s <;> simp [hn]

/-- The entire tail norm is preserved, not only the total sequence norm. -/
theorem norm_phaseMultiply_sub_truncate (s : Finset ℤ) (θ : ℤ → ℝ) (a : Coeff p) :
    ‖phaseMultiply θ a-truncate s (phaseMultiply θ a)‖ = ‖a-truncate s a‖ := by
  rw [truncate_phaseMultiply]
  change ‖phaseMultiplyLI θ a-phaseMultiplyLI θ (truncate s a)‖ = _
  rw [← map_sub, (phaseMultiplyLI θ).norm_map]

/-- Norm continuity follows from coordinatewise continuous angles and norm-continuous amplitudes. -/
theorem continuous_phaseMultiply_family {X : Type*} [TopologicalSpace X]
    (hp : p ≠ ⊤) (θ : X → ℤ → ℝ) (a : X → Coeff p)
    (hθ : ∀ n, Continuous (fun x => θ x n)) (ha : Continuous a) :
    Continuous (fun x => phaseMultiply (θ x) (a x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_coordinatewise_of_uniform_tails
  · intro n
    simp only [phaseMultiply_apply]
    exact ((((Complex.continuous_ofReal.comp (hθ n)).mul continuous_const).cexp).mul
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp ha)).continuousAt
  · intro ε hε
    obtain ⟨s,hs⟩ := ((tendsto_truncate hp (a x)).eventually (ball_mem_nhds (a x) hε)).exists
    have hsmall : ‖a x-truncate s (a x)‖ < ε := by
      simpa only [mem_ball,dist_eq_norm,norm_sub_rev] using hs
    let V := {y : X | ‖a y-truncate s (a y)‖ < ε}
    have hV : IsOpen V := isOpen_lt (ha.sub ((truncateCLM s).continuous.comp ha)).norm continuous_const
    refine ⟨s,V,hV,hsmall,?_⟩
    intro y hy
    rw [norm_phaseMultiply_sub_truncate]
    exact le_of_lt hy

/-- The diagonal phase flow for arbitrary real, possibly unbounded, frequencies. -/
def phaseFlow (ω : ℤ → ℝ) (t : ℝ) : Coeff p →ₗᵢ[ℂ] Coeff p :=
  phaseMultiplyLI (fun n => t*ω n)

@[simp] theorem phaseFlow_apply (ω : ℤ → ℝ) (t : ℝ) (a : Coeff p) (n : ℤ) :
    phaseFlow ω t a n = Complex.exp (((t*ω n : ℝ) : ℂ)*I)*a n := rfl

@[simp] theorem phaseFlow_zero (ω : ℤ → ℝ) (a : Coeff p) : phaseFlow ω 0 a = a := by
  change phaseMultiply (fun n => 0*ω n) a = a
  simpa only [zero_mul] using phaseMultiply_zero_angles a

theorem phaseFlow_add (ω : ℤ → ℝ) (t u : ℝ) (a : Coeff p) :
    phaseFlow ω t (phaseFlow ω u a) = phaseFlow ω (t+u) a := by
  change phaseMultiply _ (phaseMultiply _ a) = phaseMultiply _ a
  rw [phaseMultiply_add_angles]
  congr 1
  funext n
  ring

/-- The full time-amplitude map is continuous for each finite exponent. -/
theorem continuous_phaseFlow (hp : p ≠ ⊤) (ω : ℤ → ℝ) :
    Continuous (fun x : ℝ × Coeff p => phaseFlow ω x.1 x.2) :=
  continuous_phaseMultiply_family hp (fun x : ℝ × Coeff p => fun n => x.1*ω n) (fun x : ℝ × Coeff p => x.2)
    (fun _ => continuous_fst.mul continuous_const) continuous_snd

end NLS.Coeff
