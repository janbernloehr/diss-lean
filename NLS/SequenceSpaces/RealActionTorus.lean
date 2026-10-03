import NLS.SequenceSpaces.DominatedCompactness
import NLS.SequenceSpaces.RealActionReduction

/-! # Compact tori of fixed quadratic actions

The torus with action sequence `I` fixes the radius of each real coordinate
pair. It is compact in every finite sequence exponent. A nonempty torus
has a summable coordinate majorant obtained from any one of its elements;
closedness and norm compactness under domination then finish the proof.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real sequence torus with prescribed quadratic actions. -/
def actionTorus (p : ℝ≥0∞) (I : ℤ → ℝ) : Set (RealCoeff p × RealCoeff p) :=
  {z | ∀ n : ℤ, pairAction z n = I n}

omit [Fact (1 ≤ p)] in
@[simp] theorem mem_actionTorus_self (z : RealCoeff p × RealCoeff p) :
    z ∈ actionTorus p (pairAction z) := fun _ => rfl

theorem continuous_pairAction (n : ℤ) :
    Continuous (fun z : RealCoeff p × RealCoeff p => pairAction z n) :=
  (((lp.evalCLM ℝ (fun _ : ℤ => ℝ) p n).continuous.comp continuous_fst).pow 2 |>.add
    (((lp.evalCLM ℝ (fun _ : ℤ => ℝ) p n).continuous.comp continuous_snd).pow 2)).div_const 2

/-- Fixed actions impose closed coordinate conditions in the full norm. -/
theorem isClosed_actionTorus (I : ℤ → ℝ) : IsClosed (actionTorus p I) := by
  simp only [actionTorus,ofPred_forall]
  exact isClosed_iInter (fun n => isClosed_eq (continuous_pairAction n) continuous_const)

omit [Fact (1 ≤ p)] in
/-- Any element of a fixed-action torus bounds every other element's
coordinate magnitudes by the sum of its own component magnitudes. -/
theorem abs_coordinates_le_of_pairAction_eq (z w : RealCoeff p × RealCoeff p) (n : ℤ)
    (h : pairAction w n = pairAction z n) :
    |w.1 n| ≤ |z.1 n|+|z.2 n| ∧ |w.2 n| ≤ |z.1 n|+|z.2 n| := by
  dsimp only [pairAction] at h
  have hab := mul_nonneg (abs_nonneg (z.1 n)) (abs_nonneg (z.2 n))
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
    nlinarith [sq_abs (w.1 n),sq_abs (z.1 n),sq_abs (z.2 n),sq_nonneg (w.2 n)]
  · apply (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
    nlinarith [sq_abs (w.2 n),sq_abs (z.1 n),sq_abs (z.2 n),sq_nonneg (w.1 n)]

/-- Every action torus is norm compact at every finite exponent, including
empty tori and tori with infinitely many nonzero actions. -/
theorem isCompact_actionTorus (hp : p ≠ ⊤) (I : ℤ → ℝ) :
    IsCompact (actionTorus p I) := by
  classical
  by_cases h : (actionTorus p I).Nonempty
  · obtain ⟨z,hz⟩ := h
    let b : RealCoeff p := lp.toNorm z.1+lp.toNorm z.2
    let K : Set (RealCoeff p) := {a | ∀ n : ℤ, ‖a n‖ ≤ ‖b n‖}
    have hclosed : IsClosed K := by
      simp only [K,ofPred_forall]
      exact isClosed_iInter (fun n => isClosed_le
        ((lp.evalCLM ℝ (fun _ : ℤ => ℝ) p n).continuous.norm) continuous_const)
    have hK := isCompact_of_isClosed_of_majorant hp b hclosed (fun _ ha => ha)
    apply (hK.prod hK).of_isClosed_subset (isClosed_actionTorus I)
    intro w hw
    have hcoords (n : ℤ) := abs_coordinates_le_of_pairAction_eq z w n ((hw n).trans (hz n).symm)
    constructor <;> intro n
    · change |w.1 n| ≤ |‖z.1 n‖+‖z.2 n‖|
      rw [abs_of_nonneg (add_nonneg (norm_nonneg (z.1 n)) (norm_nonneg (z.2 n)))]
      exact (hcoords n).1
    · change |w.2 n| ≤ |‖z.1 n‖+‖z.2 n‖|
      rw [abs_of_nonneg (add_nonneg (norm_nonneg (z.1 n)) (norm_nonneg (z.2 n)))]
      exact (hcoords n).2
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact isCompact_empty

omit [Fact (1 ≤ p)] in
/-- Zero action at one index forces both coordinates there to vanish. -/
theorem coordinates_zero_of_mem_actionTorus {I : ℤ → ℝ} {z : RealCoeff p × RealCoeff p}
    (hz : z ∈ actionTorus p I) (n : ℤ) (hn : I n = 0) : z.1 n = 0 ∧ z.2 n = 0 := by
  have h := hz n
  rw [hn,pairAction] at h
  constructor <;> nlinarith [sq_nonneg (z.1 n),sq_nonneg (z.2 n)]

end NLS.RealCoeff
