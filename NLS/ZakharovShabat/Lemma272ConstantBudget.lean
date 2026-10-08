import NLS.ZakharovShabat.RefinedH1ActionBound

/-! # Exact constant arithmetic for Lemma 27.2 at orders m ≥ 2 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Two powers provide the margin needed to absorb the energy factor two. -/
theorem two_mul_eight_thirds_pow_le_four_pow (e : ℕ) (he : 2 ≤ e) :
    2*(8/3:ℝ)^e ≤ (4:ℝ)^e := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) (by norm_num : (8/3:ℝ) ≤ 4) (e-2)
  calc
    _ = (2*(8/3:ℝ)^2)*(8/3:ℝ)^(e-2) := by rw [mul_assoc, ← pow_add, show 2+(e-2) = e by omega]
    _ ≤ (4:ℝ)^2*4^(e-2) := mul_le_mul (by norm_num) hp (by positivity) (by norm_num)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- The refined physical H¹ bound preserves the printed 64π coefficient for every m ≥ 2. -/
theorem lemma272_central_budget (m : ℕ) (hm : 2 ≤ m) (P M S : ℝ)
    (hM : 0 ≤ M) (hMS : M ≤ S) (hP : P^2 ≤ (8/3:ℝ)*(S+M^2)) :
    (16*Real.pi)^(2*(m-1))*(1+P^2)^(2*(m-1))*(S+2*M^2) ≤
      (64*Real.pi)^(2*m-2)*(1+S)^(4*m-3)*S := by
  let e := 2*(m-1)
  have he : 2 ≤ e := by dsimp [e]; omega
  have hS : 0 ≤ S := hM.trans hMS
  have hsq := pow_le_pow_left₀ hM hMS 2
  have hbase : 1+P^2 ≤ (8/3:ℝ)*(1+S)^2 := by nlinarith
  have henergy : S+2*M^2 ≤ 2*(1+S)*S := by nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+P^2) hbase e
  have hc : 2*(16*Real.pi)^e*(8/3:ℝ)^e ≤ (64*Real.pi)^e := by
    calc
      _ = (16*Real.pi)^e*(2*(8/3:ℝ)^e) := by ring
      _ ≤ (16*Real.pi)^e*4^e := mul_le_mul_of_nonneg_left
        (two_mul_eight_thirds_pow_le_four_pow e he) (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; ring
  calc
    _ ≤ (16*Real.pi)^e*(((8/3:ℝ)*(1+S)^2)^e*(2*(1+S)*S)) := by
      rw [mul_assoc]
      change (16*Real.pi)^e*((1+P^2)^e*(S+2*M^2)) ≤ _
      exact mul_le_mul_of_nonneg_left (mul_le_mul hp henergy (by positivity) (by positivity)) (by positivity)
    _ = (2*(16*Real.pi)^e*(8/3:ℝ)^e)*(1+S)^(2*e+1)*S := by
      rw [mul_pow (8/3:ℝ) ((1+S)^2), ← pow_mul, pow_succ]
      ring
    _ ≤ (64*Real.pi)^e*(1+S)^(2*e+1)*S := by gcongr
    _ = _ := by
      rw [show e = 2*m-2 by dsimp [e]; omega, show 2*(2*m-2)+1 = 4*m-3 by omega]

/-- At m=1 the factor used above has no powers and cannot absorb a factor two. -/
theorem lemma272_zero_exponent_margin_fails : ¬ (2*(8/3:ℝ)^0 ≤ (4:ℝ)^0) := by norm_num

end NLS.ZakharovShabat
