import NLS.FunctionalAnalysis.RectangleIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Pole integrals around rectangles

Edge primitives and the principal logarithm compute the positively oriented
simple-pole integral. A primitive on all four edges makes higher pole terms
vanish, even when the pole lies in the interior.
-/

noncomputable section
open Complex Set MeasureTheory
namespace NLS.RectangleIntegral

/-- The fundamental theorem of calculus on a horizontal complex edge. -/
theorem horizontal_integral_eq_sub {F f : ℂ → ℂ} {a b y : ℝ}
    (hF : ∀ x ∈ uIcc a b, HasDerivAt F (f (x + y * I)) (x + y * I))
    (hi : IntervalIntegrable (fun x : ℝ => f (x + y * I)) volume a b) :
    (∫ x : ℝ in a..b, f (x + y * I)) = F (b + y * I) - F (a + y * I) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro x hx
  simpa [Function.comp_def] using! ((hF x hx).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const _)).comp_ofReal

/-- The fundamental theorem of calculus on an upward complex edge includes the factor `i`. -/
theorem vertical_integral_eq_sub {F f : ℂ → ℂ} {a b x : ℝ}
    (hF : ∀ y ∈ uIcc a b, HasDerivAt F (f (x + y * I)) (x + y * I))
    (hi : IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume a b) :
    I • (∫ y : ℝ in a..b, f (x + y * I)) = F (x + b * I) - F (x + a * I) := by
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hi.smul I)
  intro y hy
  simpa [Function.comp_def, smul_eq_mul, mul_comm] using!
    ((hF y hy).comp (y : ℂ) (((hasDerivAt_id (y : ℂ)).mul_const I).const_add _)).comp_ofReal

/-- A single primitive defined along all four edges makes the closed contour integral vanish. -/
theorem eq_zero_of_hasDerivAt {F f : ℂ → ℂ} {z w : ℂ}
    (hF : ∀ ζ ∈ boundary z w, HasDerivAt F (f ζ) ζ) (hi : Integrable f z w) :
    integral f z w = 0 := by
  unfold integral
  rw [horizontal_integral_eq_sub (fun x hx => hF _ (horizontal_mem z w hx (Or.inl rfl))) hi.bottom,
    horizontal_integral_eq_sub (fun x hx => hF _ (horizontal_mem z w hx (Or.inr rfl))) hi.top,
    vertical_integral_eq_sub (fun y hy => hF _ (vertical_mem z w hy (Or.inr rfl))) hi.right,
    vertical_integral_eq_sub (fun y hy => hF _ (vertical_mem z w hy (Or.inl rfl))) hi.left]
  abel

/-- The simple-pole kernel is continuous on any boundary avoiding its pole. -/
theorem continuousOn_inv_sub {z w a : ℂ} (ha : a ∉ boundary z w) :
    ContinuousOn (fun ζ : ℂ => (ζ - a)⁻¹) (boundary z w) :=
  (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => by
    change ζ - a ≠ 0
    exact sub_ne_zero.mpr (fun h => ha (h ▸ hζ))

private theorem log_neg_of_im_pos {a : ℂ} (ha : 0 < a.im) :
    log (-a) = log a - Real.pi * I := by
  simp only [log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos ha, ofReal_sub]
  ring

private theorem log_neg_of_im_neg {a : ℂ} (ha : a.im < 0) :
    log (-a) = log a + Real.pi * I := by
  simp only [log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg ha, ofReal_add]
  ring

/-- A counterclockwise rectangle contributes `2πi` for every strictly enclosed simple pole. -/
theorem integral_inv_sub_of_mem {z w a : ℂ}
    (ha : a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    integral (fun ζ : ℂ => (ζ - a)⁻¹) z w = 2 * Real.pi * I := by
  have hnot : a ∉ boundary z w := by
    rintro ⟨_, _, h | h | h | h⟩ <;> linarith [ha.1.1, ha.1.2, ha.2.1, ha.2.2]
  have hi := integrable_of_continuousOn (continuousOn_inv_sub hnot)
  have hh (y : ℝ) (hy : y = z.im ∨ y = w.im) (x : ℝ) :
      HasDerivAt (fun ζ : ℂ => log (ζ - a)) ((x + y * I - a)⁻¹) (x + y * I) := by
    have hs : (x : ℂ) + y * I - a ∈ slitPlane := by
      apply Or.inr
      rcases hy with rfl | rfl <;>
        simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add] <;>
        linarith [ha.2.1, ha.2.2]
    simpa using! ((hasDerivAt_id _).sub_const a).clog hs
  have hr (y : ℝ) :
      HasDerivAt (fun ζ : ℂ => log (ζ - a)) ((w.re + y * I - a)⁻¹) (w.re + y * I) := by
    have hs : (w.re : ℂ) + y * I - a ∈ slitPlane := by
      apply Or.inl
      simpa using sub_pos.mpr ha.1.2
    simpa using! ((hasDerivAt_id _).sub_const a).clog hs
  have hl (y : ℝ) :
      HasDerivAt (fun ζ : ℂ => log (a - ζ)) ((z.re + y * I - a)⁻¹) (z.re + y * I) := by
    have hs : a - ((z.re : ℂ) + y * I) ∈ slitPlane := by
      apply Or.inl
      simpa using sub_pos.mpr ha.1.1
    have he : (-1 : ℂ) / (a - ((z.re : ℂ) + y * I)) = ((z.re : ℂ) + y * I - a)⁻¹ := by
      rw [show a - ((z.re : ℂ) + y * I) = -((z.re : ℂ) + y * I - a) by ring]
      rw [neg_div_neg_eq, one_div]
    simpa only [id_eq, he] using! ((hasDerivAt_id ((z.re : ℂ) + y * I)).const_sub a).clog hs
  unfold integral
  rw [horizontal_integral_eq_sub (f := fun ζ : ℂ => (ζ - a)⁻¹) (fun x _ => hh _ (Or.inl rfl) x) hi.bottom,
    horizontal_integral_eq_sub (f := fun ζ : ℂ => (ζ - a)⁻¹) (fun x _ => hh _ (Or.inr rfl) x) hi.top,
    vertical_integral_eq_sub (f := fun ζ : ℂ => (ζ - a)⁻¹) (fun y _ => hr y) hi.right,
    vertical_integral_eq_sub (f := fun ζ : ℂ => (ζ - a)⁻¹) (fun y _ => hl y) hi.left]
  have hb : ((z.re : ℂ) + z.im * I - a).im < 0 := by simpa using sub_neg.mpr ha.2.1
  have ht : 0 < ((z.re : ℂ) + w.im * I - a).im := by simpa using sub_pos.mpr ha.2.2
  rw [show a - ((z.re : ℂ) + w.im * I) = -((z.re : ℂ) + w.im * I - a) by ring,
    show a - ((z.re : ℂ) + z.im * I) = -((z.re : ℂ) + z.im * I - a) by ring,
    log_neg_of_im_pos ht, log_neg_of_im_neg hb]
  ring

/-- A pole outside the filled rectangle contributes zero. -/
theorem integral_inv_sub_of_notMem {z w a : ℂ}
    (ha : a ∉ uIcc z.re w.re ×ℂ uIcc z.im w.im) :
    integral (fun ζ : ℂ => (ζ - a)⁻¹) z w = 0 := by
  apply eq_zero_of_differentiableOn
  intro ζ hζ
  exact ((differentiableAt_id.sub_const a).inv
    (sub_ne_zero.mpr (fun h => ha (h ▸ hζ)))).differentiableWithinAt

/-- All higher pole terms vanish around any rectangle avoiding the pole on its boundary. -/
theorem integral_inv_sub_pow_succ_succ {z w a : ℂ} (ha : a ∉ boundary z w) (k : ℕ) :
    integral (fun ζ : ℂ => (ζ - a)⁻¹ ^ (k + 2)) z w = 0 := by
  let m : ℤ := -((k : ℤ) + 1)
  have hm : (m : ℂ) ≠ 0 := by dsimp [m]; exact_mod_cast (show -((k : ℤ) + 1) ≠ 0 by omega)
  apply eq_zero_of_hasDerivAt (F := fun ζ : ℂ => (m : ℂ)⁻¹ * (ζ - a) ^ m)
  · intro ζ hζ
    have hne : ζ - a ≠ 0 := sub_ne_zero.mpr (fun h => ha (h ▸ hζ))
    have hd := (((hasDerivAt_zpow m (ζ - a) (Or.inl hne)).comp ζ
      ((hasDerivAt_id ζ).sub_const a)).const_mul (m : ℂ)⁻¹)
    have he : m - 1 = -((k + 2 : ℕ) : ℤ) := by dsimp [m]; omega
    simpa only [id_eq, mul_one, ← mul_assoc, inv_mul_cancel₀ hm, one_mul, he,
      zpow_neg, zpow_natCast, inv_pow] using! hd
  · exact integrable_of_continuousOn ((continuousOn_inv_sub ha).pow (k + 2))

end NLS.RectangleIntegral
