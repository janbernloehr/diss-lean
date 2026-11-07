import NLS.ComplexAnalysis.Rouche

/-! Quantitative error in a coupled quadratic characteristic polynomial.
The constants are chosen for the source complex ratio 1/9..9. -/
noncomputable section
namespace NLS.ComplexAnalysis

theorem coupledQuadraticError_le (ρ : ℝ) (hρ : 0≤ρ) (x a b c b₀ c₀ : ℂ)
    (hx : ‖x‖≤2*ρ) (ha : ‖a‖≤ρ/44)
    (hb : ‖b-b₀‖≤ρ/44) (hc : ‖c-c₀‖≤ρ/44)
    (hb₀ : ‖b₀‖≤3*ρ) (hc₀ : ‖c₀‖≤3*ρ) :
    ‖((x-a)^2-b*c)-(x^2-b₀*c₀)‖≤ρ^2/3 := by
  have he : ((x-a)^2-b*c)-(x^2-b₀*c₀)=
      ((-2:ℂ)*x*a+a^2)-((b-b₀)*c+b₀*(c-c₀)) := by ring
  rw [he]
  have hnorm : ‖((-2:ℂ)*x*a+a^2)-((b-b₀)*c+b₀*(c-c₀))‖≤
      2*‖x‖*‖a‖+‖a‖^2+‖b-b₀‖*‖c‖+‖b₀‖*‖c-c₀‖ := by
    have h := (norm_sub_le ((-2:ℂ)*x*a+a^2) ((b-b₀)*c+b₀*(c-c₀))).trans
      (add_le_add (norm_add_le ((-2:ℂ)*x*a) (a^2)) (norm_add_le ((b-b₀)*c) (b₀*(c-c₀))))
    simpa only [norm_mul,norm_pow,norm_neg,Complex.norm_ofNat,add_assoc] using h
  have hcfull : ‖c‖≤3*ρ+ρ/44 := by linarith [norm_le_norm_sub_add c c₀]
  have hxap := mul_le_mul hx ha (norm_nonneg _) (by positivity : (0:ℝ)≤2*ρ)
  have haap : ‖a‖^2≤(ρ/44)^2 := by nlinarith [norm_nonneg a]
  have hbcp := mul_le_mul hb hcfull (norm_nonneg _) (by positivity : (0:ℝ)≤ρ/44)
  have hbc₀p := mul_le_mul hb₀ hc (norm_nonneg _) (by positivity : (0:ℝ)≤3*ρ)
  nlinarith [sq_nonneg ρ]

end NLS.ComplexAnalysis
