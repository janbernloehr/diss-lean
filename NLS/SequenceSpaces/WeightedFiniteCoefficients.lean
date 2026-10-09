import NLS.SequenceSpaces.Weighted

/-! # Finite coefficients and continuous coordinates in weighted spaces -/
noncomputable section
open Set Filter
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞)

/-- A finite raw coefficient sequence belongs to every weighted exponent space. -/
def ofFinsupp (a : ℤ →₀ ℂ) : WeightedCoeff w p :=
  ⟨a, (memℓp_zero_iff.mpr (Function.HasFiniteSupport.mul_right
    (fun n : ℤ => (w n : ℂ)) a.hasFiniteSupport)).of_exponent_ge bot_le⟩

@[simp] theorem ofFinsupp_apply (a : ℤ →₀ ℂ) (n : ℤ) : (ofFinsupp w p a).val n = a n := rfl

/-- Finite raw coefficients are dense at each finite Banach exponent, for every positive weight. -/
theorem denseRange_ofFinsupp [Fact (1 ≤ p)] (hp : p ≠ ⊤) : DenseRange (ofFinsupp w p) := by
  intro a
  apply mem_closure_of_tendsto (tendsto_truncate w p hp a)
  apply Eventually.of_forall
  intro S
  let b : ℤ →₀ ℂ := Finsupp.onFinset S (truncate w p S a).val (by
    intro n hn
    by_contra h
    exact hn (by simp [h]))
  exact ⟨b,Subtype.ext (by rfl)⟩

/-- Evaluation of a raw weighted coefficient is a bounded complex-linear functional. -/
def evalCLM [Fact (1 ≤ p)] (n : ℤ) : WeightedCoeff w p →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => a.val n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (1/w n) (fun a => by
      change ‖a.val n‖ ≤ (1/w n)*‖a‖
      simpa [div_eq_mul_inv,mul_comm] using norm_apply_le w p a n)

@[simp] theorem evalCLM_apply [Fact (1 ≤ p)] (n : ℤ) (a : WeightedCoeff w p) :
    evalCLM w p n a = a.val n := rfl

end NLS.WeightedCoeff
