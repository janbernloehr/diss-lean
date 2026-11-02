import NLS.SequenceSpaces.WeightedPhaseFlow
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Action-dependent phase evolution in the native weighted norm

Generic dependency for arXiv:1605.06690v1, Appendix E.1 (i)-(ii).
The group law uses conservation of the squared amplitudes: arbitrary
state-dependent frequencies would not suffice. This module constructs no
KdV frequency map and asserts no equation-specific wellposedness result.
-/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal

namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coordinatewise continuous frequencies suffice, with no bound uniform in
the coordinate index, in every finite weighted Banach exponent. -/
theorem continuous_phaseFlow_family {X : Type*} [TopologicalSpace X]
    (w : Weight) (hp : p ≠ ⊤) (ω : X → ℤ → ℝ) (a : X → WeightedCoeff w p)
    (hω : ∀ n, Continuous (fun x => ω x n)) (ha : Continuous a) :
    Continuous (fun x : ℝ × X => phaseFlow w (ω x.2) x.1 (a x.2)) := by
  exact (weightIsometry w p).symm.continuous.comp
    (Coeff.continuous_phaseMultiply_family hp
      (fun x : ℝ × X => fun n => x.1 * ω x.2 n)
      (fun x => weightIsometry w p (a x.2))
      (fun n => continuous_fst.mul ((hω n).comp continuous_snd))
      ((weightIsometry w p).continuous.comp (ha.comp continuous_snd)))

/-- Squared raw amplitudes; on the signed real locus these are the actions. -/
def squaredAmplitudes {w : Weight} (a : WeightedCoeff w p) : ℤ → ℝ :=
  fun n => ‖a.val n‖ ^ 2

/-- Every real phase rotation preserves the complete amplitude sequence. -/
@[simp] theorem squaredAmplitudes_phaseFlow (w : Weight) (ω : ℤ → ℝ)
    (t : ℝ) (a : WeightedCoeff w p) :
    squaredAmplitudes (phaseFlow w ω t a) = squaredAmplitudes a := by
  funext n
  simp only [squaredAmplitudes, phaseFlow_apply, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- A nonlinear diagonal flow whose frequencies depend on squared amplitudes. -/
def actionPhaseFlow (w : Weight) (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (t : ℝ) (a : WeightedCoeff w p) : WeightedCoeff w p :=
  phaseFlow w (Ω (squaredAmplitudes a)) t a

@[simp] theorem actionPhaseFlow_apply (w : Weight) (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (t : ℝ) (a : WeightedCoeff w p) (n : ℤ) :
    (actionPhaseFlow w Ω t a).val n =
      Complex.exp (((t * Ω (squaredAmplitudes a) n : ℝ) : ℂ) * Complex.I) * a.val n :=
  phaseFlow_apply w _ t a n

@[simp] theorem squaredAmplitudes_actionPhaseFlow (w : Weight)
    (Ω : (ℤ → ℝ) → ℤ → ℝ) (t : ℝ) (a : WeightedCoeff w p) :
    squaredAmplitudes (actionPhaseFlow w Ω t a) = squaredAmplitudes a :=
  squaredAmplitudes_phaseFlow w _ t a

@[simp] theorem actionPhaseFlow_zero (w : Weight) (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (a : WeightedCoeff w p) : actionPhaseFlow w Ω 0 a = a :=
  phaseFlow_zero w _ a

/-- Conservation of the actual amplitude sequence gives the nonlinear group law. -/
theorem actionPhaseFlow_add (w : Weight) (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (t u : ℝ) (a : WeightedCoeff w p) :
    actionPhaseFlow w Ω t (actionPhaseFlow w Ω u a) = actionPhaseFlow w Ω (t + u) a := by
  simp only [actionPhaseFlow, squaredAmplitudes_phaseFlow, phaseFlow_add]

@[simp] theorem norm_actionPhaseFlow (w : Weight) (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (t : ℝ) (a : WeightedCoeff w p) : ‖actionPhaseFlow w Ω t a‖ = ‖a‖ :=
  norm_phaseFlow w _ t a

/-- Each orbit is norm continuous without any continuity assumption on Ω. -/
theorem continuous_actionPhaseFlow_orbit (w : Weight) (hp : p ≠ ⊤)
    (Ω : (ℤ → ℝ) → ℤ → ℝ) (a : WeightedCoeff w p) :
    Continuous (fun t : ℝ => actionPhaseFlow w Ω t a) := by
  change Continuous (fun t : ℝ => phaseFlow w (Ω (squaredAmplitudes a)) t a)
  have hi : Continuous (fun t : ℝ => (t, a)) := continuous_id.prodMk continuous_const
  simpa only [Function.comp_def] using!
    (continuous_phaseFlow (p := p) w hp (Ω (squaredAmplitudes a))).comp hi

/-- Joint norm continuity requires only continuity of each realized frequency. -/
theorem continuous_actionPhaseFlow (w : Weight) (hp : p ≠ ⊤)
    (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (hΩ : ∀ n, Continuous (fun a : WeightedCoeff w p => Ω (squaredAmplitudes a) n)) :
    Continuous (fun x : ℝ × WeightedCoeff w p => actionPhaseFlow w Ω x.1 x.2) := by
  change Continuous (fun x : ℝ × WeightedCoeff w p =>
    phaseFlow w (Ω (squaredAmplitudes x.2)) x.1 x.2)
  exact continuous_phaseFlow_family (p := p) w hp
    (fun a : WeightedCoeff w p => Ω (squaredAmplitudes a)) id hΩ continuous_id

/-- Compact-time trajectories in the actual weighted sequence norm. -/
def actionPhaseTrajectory (w : Weight) (hp : p ≠ ⊤)
    (Ω : (ℤ → ℝ) → ℤ → ℝ) (T : ℝ) (a : WeightedCoeff w p) :
    C(Icc (-T) T, WeightedCoeff w p) where
  toFun τ := actionPhaseFlow w Ω τ.val a
  continuous_toFun := (continuous_actionPhaseFlow_orbit w hp Ω a).comp continuous_subtype_val

/-- Continuous dependence in the uniform topology on every compact time interval. -/
theorem continuous_actionPhaseTrajectory (w : Weight) (hp : p ≠ ⊤)
    (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (hΩ : ∀ n, Continuous (fun a : WeightedCoeff w p => Ω (squaredAmplitudes a) n))
    (T : ℝ) : Continuous (actionPhaseTrajectory w hp Ω T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun x : WeightedCoeff w p × Icc (-T) T =>
    actionPhaseFlow w Ω x.2.val x.1)
  have hi : Continuous (fun x : WeightedCoeff w p × Icc (-T) T => (x.2.val, x.1)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst
  simpa only [Function.comp_def] using! (continuous_actionPhaseFlow w hp Ω hΩ).comp hi

/-- Each time slice is a homeomorphism, with inverse given by negative time. -/
def actionPhaseHomeomorph (w : Weight) (hp : p ≠ ⊤)
    (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (hΩ : ∀ n, Continuous (fun a : WeightedCoeff w p => Ω (squaredAmplitudes a) n))
    (t : ℝ) : WeightedCoeff w p ≃ₜ WeightedCoeff w p where
  toFun := actionPhaseFlow w Ω t
  invFun := actionPhaseFlow w Ω (-t)
  left_inv a := by simp only [actionPhaseFlow_add, neg_add_cancel, actionPhaseFlow_zero]
  right_inv a := by simp only [actionPhaseFlow_add, add_neg_cancel, actionPhaseFlow_zero]
  continuous_toFun := by
    have hi : Continuous (fun a : WeightedCoeff w p => (t, a)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using! (continuous_actionPhaseFlow w hp Ω hΩ).comp hi
  continuous_invFun := by
    have hi : Continuous (fun a : WeightedCoeff w p => (-t, a)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using! (continuous_actionPhaseFlow w hp Ω hΩ).comp hi

end NLS.WeightedCoeff
