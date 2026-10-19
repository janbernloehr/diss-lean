import NLS.ZakharovShabat.ClassicalScalarForcingDiagonalIdentity

/-! # A quantitative diagonal forced-response approximation

Replacing the lower response gains one inverse-frequency power with only an L1 bound on the potential derivative.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The diagonal approximation obtained by replacing the lower forced
response by a prescribed continuous scalar response. -/
def classicalDiagonalApproximation (a f S : ℝ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  (2*I*z)⁻¹*(I*a t*S t-exp (-I*z*t)*
    (∫ x in (0:ℝ)..t, exp (I*z*x)*(I*deriv a x*S x+I*a x*f x)))

/-- Replacing the lower response in the exact diagonal identity gains
one inverse-frequency power. Only the L1 norm of the potential derivative
enters this estimate. -/
theorem norm_classicalScalarForcing_diagonal_approximation_le
    (a b f S : ℝ → ℂ) (ha : ContDiff ℝ 1 a) (hb : Continuous b)
    (hf : Continuous f) (hS : Continuous S) (z : ℂ) (hz : z ≠ 0)
    (A B E L : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hab : ∀ x ∈ Icc (0:ℝ) 1, ‖a x‖ ≤ A ∧ ‖b x‖ ≤ A)
    (hexp : ∀ x ∈ Icc (0:ℝ) 1, ‖exp (I*z*x)‖ ≤ B ∧ ‖exp (-I*z*x)‖ ≤ B)
    (hder : (∫ x in (0:ℝ)..1, ‖deriv a x‖) ≤ L)
    (herr : ∀ t : Icc (0:ℝ) 1,
      ‖classicalForcedKernelSolution (classicalPotentialOfFunctions a b ha.continuous hb)
        (classicalScalarForcing f hf) z t-(0,S t)‖ ≤ E)
    (t : Icc (0:ℝ) 1) :
    ‖(classicalForcedKernelSolution (classicalPotentialOfFunctions a b ha.continuous hb)
      (classicalScalarForcing f hf) z t).1-classicalDiagonalApproximation a f S z t‖ ≤
      ‖(2*I*z)⁻¹‖*(A+B^2*(L+A^2))*E := by
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb
  let Y := classicalForcedKernelSolution Φ (classicalScalarForcing f hf) z
  let w := (2*I*z)⁻¹
  let J := ∫ x in (0:ℝ)..t.val, exp (I*z*x)*
    (I*deriv a x*((Y x).2-S x)+a x*b x*(Y x).1)
  have hY : Continuous Y := continuous_classicalForcedKernelSolution _ _ _
  have hda : Continuous (deriv a) := ha.continuous_deriv (by norm_num)
  have h₁ (x : Icc (0:ℝ) 1) : ‖(Y x).1‖ ≤ E := by
    simpa only [Prod.fst_sub,sub_zero] using (norm_fst_le (Y x-(0,S x))).trans (herr x)
  have h₂ (x : Icc (0:ℝ) 1) : ‖(Y x).2-S x‖ ≤ E :=
    (norm_snd_le (Y x-(0,S x))).trans (herr x)
  have hJ : J =
      (∫ x in (0:ℝ)..t.val, exp (I*z*x)*
        (I*deriv a x*(Y x).2+a x*b x*(Y x).1+I*a x*f x))-
      (∫ x in (0:ℝ)..t.val, exp (I*z*x)*(I*deriv a x*S x+I*a x*f x)) := by
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hid := classicalScalarForcing_fst_integral_identity a b f ha hb hf z t
  have he := congrArg (fun u : ℂ => w*u) hid
  have hw : w*(2*I*z) = 1 := inv_mul_cancel₀ (by simp [hz])
  change w*((2*I*z)*(Y t).1) = _ at he
  rw [← mul_assoc,hw,one_mul] at he
  have hd : (Y t).1-classicalDiagonalApproximation a f S z t =
      w*(I*a t*((Y t).2-S t)-exp (-I*z*t.val)*J) := by
    rw [he,hJ]
    dsimp only [classicalDiagonalApproximation,w,Y,Φ]
    ring
  have hJn : ‖J‖ ≤ B*E*(L+A^2) := by
    let g (x : ℝ) : ℂ := ((‖deriv a x‖+A^2 : ℝ):ℂ)
    have hg : Continuous g := by dsimp only [g]; fun_prop
    have hgn (x : ℝ) : ‖g x‖ = ‖deriv a x‖+A^2 := by
      simp only [g,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ ‖deriv a x‖+A^2)]
    have hi := norm_integral_unit_le_mul_integral_norm
      (fun x => exp (I*z*x)*(I*deriv a x*((Y x).2-S x)+a x*b x*(Y x).1))
      (by fun_prop) g hg (B*E) (by positivity) (fun x hx => by
        let u : Icc (0:ℝ) 1 := ⟨x,hx⟩
        have hsum : ‖I*deriv a x*((Y x).2-S x)+a x*b x*(Y x).1‖ ≤
            ‖deriv a x‖*E+A^2*E := by
          apply (norm_add_le _ _).trans
          simp only [norm_mul,norm_I,one_mul]
          apply add_le_add (mul_le_mul_of_nonneg_left (h₂ u) (norm_nonneg _))
          apply mul_le_mul _ (h₁ u) (norm_nonneg _) (sq_nonneg A)
          simpa only [pow_two] using mul_le_mul (hab x hx).1 (hab x hx).2 (norm_nonneg _) hA
        rw [norm_mul,hgn]
        calc
          _ ≤ B*(‖deriv a x‖*E+A^2*E) :=
            mul_le_mul (hexp x hx).1 hsum (norm_nonneg _) hB
          _ = _ := by ring) t
    change ‖J‖ ≤ _ at hi
    simp_rw [hgn] at hi
    rw [intervalIntegral.integral_add (hda.norm.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),intervalIntegral.integral_const] at hi
    simp only [sub_zero,smul_eq_mul,one_mul] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (add_le_add hder le_rfl) (by positivity))
  change ‖(Y t).1-classicalDiagonalApproximation a f S z t‖ ≤ _
  rw [hd,norm_mul]
  have ht : ‖I*a t*((Y t).2-S t)-exp (-I*z*t.val)*J‖ ≤ A*E+B*(B*E*(L+A^2)) := by
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_I,one_mul]
    exact add_le_add
      (mul_le_mul (hab t t.property).1 (h₂ t) (norm_nonneg _) hA)
      (mul_le_mul (hexp t t.property).2 hJn (norm_nonneg _) hB)
  calc
    _ ≤ ‖w‖*(A*E+B*(B*E*(L+A^2))) := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = _ := by ring

end NLS.ZakharovShabat
