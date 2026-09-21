import NLS.ZakharovShabat.ClassicalSeparatedCharacteristics
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Real-type symmetry of the classical monodromy
At a real spectral parameter the system commutes with conjugation followed
by exchange of components. Uniqueness transfers this symmetry to the
fundamental columns, making both the trace and anti-discriminant real.
-/

noncomputable section
open Set Complex Matrix
open NLS.LinearVolterra
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- Conjugating and exchanging components preserves the real-parameter initial-value problem. -/
theorem classicalSolution_conj_swap (Φ : Curve (ℂ × ℂ))
    (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution Φ x (conj v.2,conj v.1) t =
      (conj (classicalSolution Φ x v t).2,conj (classicalSolution Φ x v t).1) := by
  have he := classicalSolution_unique Φ x (conj v.2,conj v.1)
    (fun s => (conj (classicalSolution Φ x v s).2,conj (classicalSolution Φ x v s).1))
    (((continuous_classicalSolution Φ x v).snd.star.prodMk
      (continuous_classicalSolution Φ x v).fst.star).continuousOn) (by simp) (by
      intro s _
      have hd := hasDerivAt_classicalSolution Φ x v s
      have hc := (HasFDerivAt.hasDerivAt hd.snd).star.prodMk (HasFDerivAt.hasDerivAt hd.fst).star
      convert! hc using 1
      apply Prod.ext <;>
        simp only [classicalODECoefficient_apply,ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply,one_smul] <;> dsimp <;>
        simp [hΦ s,map_add,map_mul,map_neg,conj_I] <;> ring)
  exact (he t.property).symm

/-- The fundamental columns have the conjugate symmetry of a real-type potential. -/
theorem classicalFundamentalMatrix_realType (Φ : Curve (ℂ × ℂ))
    (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ) (t : Icc (0 : ℝ) 1) :
    (classicalFundamentalMatrix Φ x t) 1 1 = conj ((classicalFundamentalMatrix Φ x t) 0 0) ∧
      (classicalFundamentalMatrix Φ x t) 0 1 = conj ((classicalFundamentalMatrix Φ x t) 1 0) := by
  have he := classicalSolution_conj_swap Φ hΦ x (1,0) t
  simp only [map_zero,map_one] at he
  exact ⟨congrArg Prod.snd he,congrArg Prod.fst he⟩

/-- The endpoint matrix inherits the two exact conjugation identities. -/
theorem classicalMonodromy_realType (Φ : Curve (ℂ × ℂ))
    (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ) :
    (classicalMonodromy Φ x) 1 1 = conj ((classicalMonodromy Φ x) 0 0) ∧
      (classicalMonodromy Φ x) 0 1 = conj ((classicalMonodromy Φ x) 1 0) :=
  classicalFundamentalMatrix_realType Φ hΦ x ⟨1,by constructor <;> norm_num⟩

/-- At real spectral parameters the classical discriminant is real. -/
theorem classicalDiscriminant_im_eq_zero (Φ : Curve (ℂ × ℂ))
    (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ) : (classicalDiscriminant Φ x).im = 0 := by
  simp only [classicalDiscriminant,Matrix.trace_fin_two,(classicalMonodromy_realType Φ hΦ x).1,
    add_im,conj_im,add_neg_cancel]

/-- At real spectral parameters the classical anti-discriminant is real. -/
theorem classicalAntiDiscriminant_im_eq_zero (Φ : Curve (ℂ × ℂ))
    (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ) : (classicalAntiDiscriminant Φ x).im = 0 := by
  simp only [classicalAntiDiscriminant,(classicalMonodromy_realType Φ hΦ x).2,
    add_im,conj_im,neg_add_cancel]

/-- Both separated characteristics are real along the real spectral axis. -/
theorem classicalSeparatedCharacteristic_im_eq_zero (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ) :
    (classicalSeparatedCharacteristic b Φ x).im = 0 := by
  have he := classicalMonodromy_realType Φ hΦ x
  cases b <;> simp [classicalSeparatedCharacteristic,BoundaryCondition.extensionSign,he.1,he.2,
    Complex.div_im,mul_re,mul_im]

end NLS.ZakharovShabat
