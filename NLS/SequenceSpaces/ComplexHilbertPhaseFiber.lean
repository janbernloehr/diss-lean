import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Continuous invariants of complex Hilbert magnitude fibers

Finite single-coordinate phase rotations are smooth and connect every
finite block of two equal-magnitude sequences. Their finite splices
converge in the actual Hilbert norm, so a continuous invariant of these
rotations depends only on the complete coordinate magnitudes.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ComplexHilbert
variable {ι : Type*} [DecidableEq ι]

/-- Rotate exactly one actual Hilbert coordinate. -/
def rotate (z : lp (fun _ : ι => ℂ) 2) (k : ι) (t : ℝ) : lp (fun _ : ι => ℂ) 2 :=
  z+lp.single 2 k ((exp ((t : ℂ)*I)-1)*z k)

@[simp] theorem rotate_same (z : lp (fun _ : ι => ℂ) 2) (k : ι) (t : ℝ) :
    rotate z k t k=exp ((t : ℂ)*I)*z k := by
  simp only [rotate,lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_eq_same]
  ring

@[simp] theorem rotate_other (z : lp (fun _ : ι => ℂ) 2) (k j : ι) (h : j≠k) (t : ℝ) :
    rotate z k t j=z j := by simp [rotate,lp.single_apply,h]

@[simp] theorem rotate_zero (z : lp (fun _ : ι => ℂ) 2) (k : ι) : rotate z k 0=z := by
  ext j
  by_cases h : j=k
  · subst j; simp
  · exact rotate_other z k j h 0

theorem norm_rotate_coordinate (z : lp (fun _ : ι => ℂ) 2) (k j : ι) (t : ℝ) :
    ‖rotate z k t j‖=‖z j‖ := by
  by_cases h : j=k
  · subst j; simp
  · rw [rotate_other z k j h]

/-- The actual single-mode phase curve is differentiable in Hilbert norm. -/
theorem hasDerivAt_rotate (z : lp (fun _ : ι => ℂ) 2) (k : ι) (t : ℝ) :
    HasDerivAt (rotate z k) (lp.single 2 k (exp ((t : ℂ)*I)*I*z k)) t := by
  have hd := ((((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).cexp.sub_const 1).mul_const (z k))
  have h := (((lp.singleContinuousLinearMap ℂ (fun _ : ι => ℂ) 2 k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd).const_add z
  simpa only [rotate,ContinuousLinearMap.coe_restrictScalars,Function.comp_apply,
    lp.singleContinuousLinearMap_apply,Complex.ofRealCLM_apply,ofReal_one,one_mul] using! h

private theorem exists_phase_mul_eq (a b : ℂ) (h : ‖a‖=‖b‖) :
    ∃ t : ℝ, exp ((t : ℂ)*I)*a=b := by
  refine ⟨b.arg-a.arg,?_⟩
  calc
    _ = exp (((b.arg-a.arg : ℝ) : ℂ)*I)*((‖a‖ : ℂ)*exp ((a.arg : ℂ)*I)) :=
      congrArg (fun c => exp (((b.arg-a.arg : ℝ) : ℂ)*I)*c) (norm_mul_exp_arg_mul_I a).symm
    _ = (‖a‖ : ℂ)*exp (((b.arg-a.arg : ℝ) : ℂ)*I+(a.arg : ℂ)*I) := by rw [exp_add]; ring
    _ = (‖b‖ : ℂ)*exp ((b.arg : ℂ)*I) := by rw [h]; congr 2; push_cast; ring
    _ = b := norm_mul_exp_arg_mul_I b

/-- Any continuous invariant of single-mode rotations is constant on
EVERY full equal-magnitude fiber, including infinite support and zeros. -/
theorem eq_of_coordinate_norm_eq {F : Type*} [TopologicalSpace F] [T2Space F]
    (f : lp (fun _ : ι => ℂ) 2 → F) (hf : Continuous f)
    (hrot : ∀ z k t, f (rotate z k t)=f z)
    (z w : lp (fun _ : ι => ℂ) 2) (h : ∀ k, ‖z k‖=‖w k‖) : f z=f w := by
  let splice := fun A : Finset ι => z+∑ j∈A, lp.single 2 j (w j-z j)
  have happly (A : Finset ι) (k : ι) : splice A k=if k∈A then w k else z k := by
    change z k+(lp.evalₗ (𝕜 := ℂ) (fun _ : ι => ℂ) 2 k) (∑ j∈A,lp.single 2 j (w j-z j))=_
    rw [map_sum]
    simp only [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]
    by_cases hk : k∈A <;> simp [hk]
  have hinv (A : Finset ι) : f (splice A)=f z := by
    induction A using Finset.induction_on with
    | empty => simp [splice]
    | @insert k A hk ih =>
      obtain ⟨t,ht⟩ := exists_phase_mul_eq (splice A k) (w k) (by rw [happly,if_neg hk,h k])
      have he : rotate (splice A) k t=splice (insert k A) := by
        ext j
        by_cases hj : j=k
        · subst j
          rw [rotate_same,ht,happly,if_pos (Finset.mem_insert_self _ _)]
        · rw [rotate_other _ k j hj,happly,happly]
          simp [hj]
      rw [←he,hrot,ih]
  have ht : Tendsto splice atTop (𝓝 w) := by
    have hh := (tendsto_const_nhds (x := z)).add (lp.hasSum_single (by simp : (2 : ℝ≥0∞)≠⊤) (w-z))
    simpa only [SummationFilter.unconditional_filter,splice,lp.coeFn_sub,Pi.sub_apply,add_sub_cancel] using! hh
  have he : IsClosed {a | f a=f z} := isClosed_eq hf continuous_const
  exact (he.mem_of_tendsto ht (Eventually.of_forall hinv)).symm

end NLS.ComplexHilbert
