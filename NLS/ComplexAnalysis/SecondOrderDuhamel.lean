import NLS.ComplexAnalysis.ScalarDuhamel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! Sine/cosine variation of constants for the ACTUAL scalar second-order
state, with zero initial position and derivative. Only continuity and
interior first derivatives are needed; no smallness condition is used. -/
noncomputable section
open Set Complex MeasureTheory intervalIntegral
namespace NLS.ComplexAnalysis

theorem secondOrder_characteristic_duhamel (F G g : ℝ → ℂ) (z a : ℂ)
    (ha : a^2 = -z^2) (t : ℝ) (ht : 0 ≤ t)
    (hF : Continuous F) (hG : Continuous G) (hg : Continuous g)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0)
    (hdF : ∀ s ∈ Ioo 0 t, HasDerivAt F (G s) s)
    (hdG : ∀ s ∈ Ioo 0 t, HasDerivAt G (-z^2*F s+g s) s) :
    G t+a*F t = ∫ s in (0:ℝ)..t, exp (a*(t-s))*g s := by
  have hd (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt (fun x => G x+a*F x) (a*(G s+a*F s)+g s) s := by
    have h := (hdG s hs).add ((hdF s hs).const_mul a)
    have he : (-z^2*F s+g s)+a*G s = a*(G s+a*F s)+g s := by
      linear_combination -(F s)*ha
    rw [he] at h
    exact h
  have h := scalar_duhamel a (fun x => G x+a*F x) g t ht (hG.add (hF.const_mul a)) hg hd
  simpa only [hF0,hG0,mul_zero,add_zero,zero_add] using h

theorem secondOrder_duhamel (F G g : ℝ → ℂ) (z : ℂ) (hz : z ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) (hF : Continuous F) (hG : Continuous G) (hg : Continuous g)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0)
    (hdF : ∀ s ∈ Ioo 0 t, HasDerivAt F (G s) s)
    (hdG : ∀ s ∈ Ioo 0 t, HasDerivAt G (-z^2*F s+g s) s) :
    F t = ∫ s in (0:ℝ)..t, (sin (z*(t-s))/z)*g s ∧
      G t = ∫ s in (0:ℝ)..t, cos (z*(t-s))*g s := by
  have hp := secondOrder_characteristic_duhamel F G g z (I*z)
    (by rw [mul_pow,I_sq]; ring) t ht hF hG hg hF0 hG0 hdF hdG
  have hm := secondOrder_characteristic_duhamel F G g z (-I*z)
    (by rw [mul_pow,neg_sq,I_sq]; ring) t ht hF hG hg hF0 hG0 hdF hdG
  let P := ∫ s in (0:ℝ)..t, exp (I*z*(t-s))*g s
  let M := ∫ s in (0:ℝ)..t, exp (-I*z*(t-s))*g s
  have hP : IntervalIntegrable (fun s : ℝ => exp (I*z*(t-s))*g s) volume 0 t :=
    (show Continuous (fun s : ℝ => exp (I*z*(t-s))*g s) by fun_prop).intervalIntegrable _ _
  have hM : IntervalIntegrable (fun s : ℝ => exp (-I*z*(t-s))*g s) volume 0 t :=
    (show Continuous (fun s : ℝ => exp (-I*z*(t-s))*g s) by fun_prop).intervalIntegrable _ _
  have heP (s : ℝ) : exp (I*z*(t-s)) = cos (z*(t-s))+I*sin (z*(t-s)) := by
    rw [show I*z*(t-s) = (z*(t-s))*I by ring,exp_mul_I]
    ring
  have heM (s : ℝ) : exp (-I*z*(t-s)) = cos (z*(t-s))-I*sin (z*(t-s)) := by
    rw [show -I*z*(t-s) = (-(z*(t-s)))*I by ring,exp_mul_I,cos_neg,sin_neg]
    ring
  have hden : (2:ℂ)*I*z ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hz
  have hFt : F t = (P-M)/(2*I*z) := by
    apply (eq_div_iff hden).mpr
    change G t+I*z*F t = P at hp
    change G t+-I*z*F t = M at hm
    linear_combination hp-hm
  have hGt : G t = (P+M)/2 := by
    apply (eq_div_iff (by norm_num : (2:ℂ) ≠ 0)).mpr
    change G t+I*z*F t = P at hp
    change G t+-I*z*F t = M at hm
    linear_combination hp+hm
  have hFi : (∫ s in (0:ℝ)..t, (sin (z*(t-s))/z)*g s) = (P-M)/(2*I*z) := by
    dsimp only [P,M]
    rw [← intervalIntegral.integral_sub hP hM,← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [heP,heM]
    field_simp [hz]
    ring
  have hGi : (∫ s in (0:ℝ)..t, cos (z*(t-s))*g s) = (P+M)/2 := by
    dsimp only [P,M]
    rw [← intervalIntegral.integral_add hP hM,← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [heP,heM]
    ring
  exact ⟨hFt.trans hFi.symm,hGt.trans hGi.symm⟩

end NLS.ComplexAnalysis
