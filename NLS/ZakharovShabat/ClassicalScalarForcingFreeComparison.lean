import NLS.ComplexAnalysis.IntegralMajorantUnit
import NLS.ZakharovShabat.ClassicalForcedKernel
import NLS.ZakharovShabat.ClassicalFirstBorn

/-! # The scalar forced solution and its free oscillatory integral

Actual fundamental-column bounds and their free errors control the explicit scalar forcing response.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The scalar forcing in the second component, restricted to the physical period. -/
def classicalScalarForcing (f : ℝ → ℂ) (hf : Continuous f) : Curve (ℂ × ℂ) :=
  ⟨fun x => (0,f x),continuous_const.prodMk (hf.comp continuous_subtype_val)⟩

/-- A uniform fundamental-column error controls the scalar forced solution's
error from its explicit free oscillatory integral. -/
theorem norm_classicalScalarForcing_sub_free_le
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (f : ℝ → ℂ) (hf : Continuous f)
    (B E : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hsol : ∀ v : ℂ × ℂ, ‖v‖ ≤ 1 → ∀ t : Icc (0:ℝ) 1, ‖classicalSolution Φ z v t‖ ≤ B)
    (herr : ∀ v : ℂ × ℂ, ‖v‖ ≤ 1 → ∀ t : Icc (0:ℝ) 1,
      ‖classicalSolution Φ z v t-classicalFreeVector z v t‖ ≤ E)
    (hfree : ∀ x ∈ Icc (0:ℝ) 1, ‖exp (-I*z*x)‖ ≤ B) (t : Icc (0:ℝ) 1) :
    ‖classicalForcedKernelSolution Φ (classicalScalarForcing f hf) z t-
      (0,exp (I*z*t.val)*(∫ x in (0:ℝ)..t.val, exp (-I*z*x)*f x))‖ ≤
        3*B*E*(∫ x in (0:ℝ)..1, ‖f x‖) := by
  let g := classicalScalarForcing f hf
  let A := classicalSolution Φ z (1,0)
  let Bc := classicalSolution Φ z (0,1)
  let e (x : ℝ) := exp (-I*z*x)
  let F := ∫ x in (0:ℝ)..t.val, e x*f x
  let D := ∫ x in (0:ℝ)..1, ‖f x‖
  let P := classicalForcedKernelPrimitive Φ g z t
  have he : Continuous e := by dsimp only [e]; fun_prop
  have hv : Continuous (fun x : ℝ => (0,e x*f x) : ℝ → ℂ × ℂ) :=
    continuous_const.prodMk (he.mul hf)
  have hP : ‖P-(0,F)‖ ≤ E*D := by
    have hint : (∫ x in (0:ℝ)..t.val, ((0:ℂ),e x*f x)) = ((0:ℂ),F) := by
      exact (ContinuousLinearMap.inr ℂ ℂ ℂ).intervalIntegral_comp_comm ((he.mul hf).intervalIntegrable _ _)
    rw [← hint]
    change ‖(∫ x in (0:ℝ)..t.val, classicalForcedKernelIntegrand Φ g z x)-
      (∫ x in (0:ℝ)..t.val, (0,e x*f x))‖ ≤ _
    rw [← intervalIntegral.integral_sub ((continuous_classicalForcedKernelIntegrand Φ g z).intervalIntegrable _ _) (hv.intervalIntegrable _ _)]
    apply norm_integral_unit_le_mul_integral_norm _ ((continuous_classicalForcedKernelIntegrand Φ g z).sub hv) f hf E hE _ t
    intro x hx
    let u : Icc (0:ℝ) 1 := ⟨x,hx⟩
    have h1 := (norm_fst_le _).trans (herr (1,0) (by simp) u)
    have h2 := (norm_fst_le _).trans (herr (0,1) (by simp) u)
    simp only [Prod.fst_sub,classicalFreeVector,mul_one,mul_zero,sub_zero] at h1 h2
    change ‖classicalForcedKernelIntegrand Φ g z u-(0,e u*f u)‖ ≤ _
    simp only [classicalForcedKernelIntegrand,extend_coe,g,classicalScalarForcing,ContinuousMap.coe_mk,
      Prod.fst_sub,Prod.snd_sub,Prod.norm_def,mul_zero,zero_sub,zero_add,sub_zero]
    apply max_le
    · simpa only [norm_neg,norm_mul] using mul_le_mul_of_nonneg_right h2 (norm_nonneg (f u))
    · rw [← sub_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg (f u))
  have hF : ‖F‖ ≤ B*D := norm_integral_unit_le_mul_integral_norm _ (he.mul hf) f hf B hB
    (fun x hx => by change ‖e x*f x‖ ≤ _; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hfree x hx) (norm_nonneg _)) t
  have hp1 : ‖P.1‖ ≤ E*D := by simpa using (norm_fst_le (P-(0,F))).trans hP
  have hp2 : ‖P.2-F‖ ≤ E*D := (norm_snd_le (P-(0,F))).trans hP
  have hA := hsol (1,0) (by simp) t
  have hBc := hsol (0,1) (by simp) t
  have hBe := herr (0,1) (by simp) t
  have hid : classicalForcedKernelSolution Φ g z t-(0,exp (I*z*t.val)*F) =
      P.1 • A t+(P.2-F) • Bc t+F • (Bc t-classicalFreeVector z (0,1) t) := by
    apply Prod.ext <;> simp [classicalForcedKernelSolution,P,A,Bc,classicalFreeVector] <;> ring
  rw [hid]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_smul]
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)
  calc
    _ ≤ (E*D)*B+(E*D)*B+(B*D)*E := add_le_add
      (add_le_add (mul_le_mul hp1 hA (norm_nonneg _) (by positivity))
        (mul_le_mul hp2 hBc (norm_nonneg _) (by positivity)))
      (mul_le_mul hF hBe (norm_nonneg _) (by positivity))
    _ = _ := by ring

end NLS.ZakharovShabat
