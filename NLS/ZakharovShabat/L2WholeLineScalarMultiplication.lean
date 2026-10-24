import NLS.ZakharovShabat.L2WholeLineScalarMaps

/-! # Bounded scalar multiplication on the whole line

A continuous uniformly bounded function acts on the original scalar L2
space, with its literal almost-everywhere product and operator bound.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLS.ZakharovShabat

private theorem memLp_wholeLineScalarMul (P : ℝ → ℂ) (hP : Continuous P)
    (C : ℝ) (hC : ∀ t, ‖P t‖ ≤ C) (f : WholeLineScalarL2) :
    MemLp (fun t => P t * f t) 2 volume := by
  apply (Lp.memLp f).of_le_mul (c := C)
    (hP.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun t => by
    simp only [Pi.mul_apply,norm_mul]
    exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _)

/-- The actual product as a scalar L2 class. -/
def wholeLineScalarMul (P : ℝ → ℂ) (hP : Continuous P)
    (C : ℝ) (hC : ∀ t, ‖P t‖ ≤ C) (f : WholeLineScalarL2) : WholeLineScalarL2 :=
  (memLp_wholeLineScalarMul P hP C hC f).toLp (fun t => P t * f t)

theorem wholeLineScalarMul_ae (P : ℝ → ℂ) (hP : Continuous P)
    (C : ℝ) (hC : ∀ t, ‖P t‖ ≤ C) (f : WholeLineScalarL2) :
    wholeLineScalarMul P hP C hC f =ᵐ[volume] (fun t => P t * f t) :=
  (memLp_wholeLineScalarMul P hP C hC f).coeFn_toLp

theorem norm_wholeLineScalarMul_le (P : ℝ → ℂ) (hP : Continuous P)
    (C : ℝ) (hC : ∀ t, ‖P t‖ ≤ C) (f : WholeLineScalarL2) :
    ‖wholeLineScalarMul P hP C hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [wholeLineScalarMul_ae P hP C hC f] with t ht
  rw [ht,norm_mul]
  exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _)

/-- Uniformly bounded continuous factors define bounded complex-linear maps. -/
def wholeLineScalarMulCLM (P : ℝ → ℂ) (hP : Continuous P)
    (C : ℝ) (hC : ∀ t, ‖P t‖ ≤ C) : WholeLineScalarL2 →L[ℂ] WholeLineScalarL2 :=
  LinearMap.mkContinuous
    { toFun := wholeLineScalarMul P hP C hC
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [wholeLineScalarMul_ae P hP C hC (f+g),
          wholeLineScalarMul_ae P hP C hC f,wholeLineScalarMul_ae P hP C hC g,
          Lp.coeFn_add f g,Lp.coeFn_add (wholeLineScalarMul P hP C hC f)
            (wholeLineScalarMul P hP C hC g)] with t hfg hf hg ha hb
        simp only [hfg,hb,Pi.add_apply,ha,hf,hg,mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [wholeLineScalarMul_ae P hP C hC (c • f),
          wholeLineScalarMul_ae P hP C hC f,Lp.coeFn_smul c f,
          Lp.coeFn_smul c (wholeLineScalarMul P hP C hC f)] with t hcf hf hc hd
        simp only [hcf,hd,Pi.smul_apply,hc,hf,smul_eq_mul,mul_left_comm,
          RingHom.id_apply] }
    C (norm_wholeLineScalarMul_le P hP C hC)

theorem wholeLineScalarMulCLM_ae (P : ℝ → ℂ) (hP : Continuous P)
    (C : ℝ) (hC : ∀ t, ‖P t‖ ≤ C) (f : WholeLineScalarL2) :
    wholeLineScalarMulCLM P hP C hC f =ᵐ[volume] (fun t => P t * f t) :=
  wholeLineScalarMul_ae P hP C hC f

end NLS.ZakharovShabat
