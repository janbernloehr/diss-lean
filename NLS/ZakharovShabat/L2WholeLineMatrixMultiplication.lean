import NLS.ZakharovShabat.L2WholeLineScalarMultiplication
import Mathlib.Analysis.Matrix.Normed

/-! # Bounded matrix multiplication on the physical whole-line L2 space -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- Matrix action in the original ordered pair coordinates. -/
def wholeLineMatrixAction (M : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (M 0 0*v.1+M 0 1*v.2,M 1 0*v.1+M 1 1*v.2)

theorem wholeLineMatrixAction_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ × ℂ) :
    wholeLineMatrixAction M (wholeLineMatrixAction N v) = wholeLineMatrixAction (M*N) v := by
  ext <;> simp only [wholeLineMatrixAction,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

@[simp] theorem wholeLineMatrixAction_one (v : ℂ × ℂ) : wholeLineMatrixAction 1 v = v := by
  ext <;> simp [wholeLineMatrixAction]

theorem wholeLineMatrixAction_columns (M : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ × ℂ) :
    wholeLineMatrixAction M v = v.1 • (M 0 0,M 1 0)+v.2 • (M 0 1,M 1 1) := by
  ext <;> simp [wholeLineMatrixAction,mul_comm]

private def wholeLineMatrixEntryMul (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hM : Continuous M) (C : ℝ) (hC : ∀ t, ‖M t‖ ≤ C) (i j : Fin 2) :
    WholeLineScalarL2 →L[ℂ] WholeLineScalarL2 :=
  wholeLineScalarMulCLM (fun t => M t i j)
    ((continuous_apply j).comp ((continuous_apply i).comp hM)) C
    (fun t => (Matrix.norm_entry_le_entrywise_sup_norm (M t)).trans (hC t))

/-- The actual uniformly bounded matrix field acts on the original L2 space. -/
def wholeLineMatrixMulCLM (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hM : Continuous M) (C : ℝ) (hC : ∀ t, ‖M t‖ ≤ C) : WholeLineL2 →L[ℂ] WholeLineL2 :=
  wholeLineFirstEmbedding.comp
    ((wholeLineMatrixEntryMul M hM C hC 0 0).comp wholeLineFirstCoordinate+
      (wholeLineMatrixEntryMul M hM C hC 0 1).comp wholeLineSecondCoordinate)+
  wholeLineSecondEmbedding.comp
    ((wholeLineMatrixEntryMul M hM C hC 1 0).comp wholeLineFirstCoordinate+
      (wholeLineMatrixEntryMul M hM C hC 1 1).comp wholeLineSecondCoordinate)

theorem wholeLineL2Pair_add_ae (f g : WholeLineL2) :
    wholeLineL2Pair (f+g) =ᵐ[volume] (fun t => wholeLineL2Pair f t+wholeLineL2Pair g t) := by
  filter_upwards [Lp.coeFn_add f g] with t ht
  exact congrArg WithLp.ofLp ht

/-- This bounded operator has the literal physical matrix product almost everywhere. -/
theorem wholeLineMatrixMulCLM_pair_ae (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hM : Continuous M) (C : ℝ) (hC : ∀ t, ‖M t‖ ≤ C) (f : WholeLineL2) :
    wholeLineL2Pair (wholeLineMatrixMulCLM M hM C hC f) =ᵐ[volume]
      (fun t => wholeLineMatrixAction (M t) (wholeLineL2Pair f t)) := by
  let a := wholeLineFirstCoordinate f
  let b := wholeLineSecondCoordinate f
  let p := wholeLineMatrixEntryMul M hM C hC 0 0 a
  let q := wholeLineMatrixEntryMul M hM C hC 0 1 b
  let r := wholeLineMatrixEntryMul M hM C hC 1 0 a
  let s := wholeLineMatrixEntryMul M hM C hC 1 1 b
  change wholeLineL2Pair (wholeLineFirstEmbedding (p+q)+wholeLineSecondEmbedding (r+s)) =ᵐ[volume] _
  filter_upwards [wholeLineL2Pair_add_ae (wholeLineFirstEmbedding (p+q))
      (wholeLineSecondEmbedding (r+s)),wholeLineFirstEmbedding_pair_ae (p+q),
    wholeLineSecondEmbedding_pair_ae (r+s),Lp.coeFn_add p q,Lp.coeFn_add r s,
    wholeLineScalarMulCLM_ae (fun t => M t 0 0) _ C _ a,
    wholeLineScalarMulCLM_ae (fun t => M t 0 1) _ C _ b,
    wholeLineScalarMulCLM_ae (fun t => M t 1 0) _ C _ a,
    wholeLineScalarMulCLM_ae (fun t => M t 1 1) _ C _ b,
    wholeLineFirstCoordinate_ae f,wholeLineSecondCoordinate_ae f]
    with t hadd hfirst hsecond hpq hrs hp hq hr hs ha hb
  rw [hadd,hfirst,hsecond]
  simp only [hpq,hrs,Pi.add_apply,Prod.mk_add_mk,add_zero,zero_add]
  change (p t+q t,r t+s t) = _ at ⊢
  dsimp only [p,q,r,s,wholeLineMatrixEntryMul] at ⊢
  rw [hp,hq,hr,hs,ha,hb]
  rfl

end NLS.ZakharovShabat
