import NLS.ZakharovShabat.SourceActionMomentComparison

/-! # The unweighted mass remainder needed in Theorem 23.2(ii) -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Splitting at unit total action converts the H¹ remainder to a top moment
and an error with an unweighted final factor. -/
theorem unweighted_action_remainder_budget (e : ℕ) (he : 2 ≤ e) (P M S T : ℝ)
    (hM : 0 ≤ M) (hMS : M ≤ S) (hT : 0 ≤ T)
    (hP : P^2 ≤ 3*(S+M^2))
    (hinter : (1+S)^e*S ≤ T+(1+S)^(e+2)*M) :
    (1+P^2)^e*(S+2*M^2) ≤ 3*6^e*(T+(1+S)^(2*e+1)*M) := by
  let B := 1+S
  have hS : 0 ≤ S := hM.trans hMS
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hM2 : M^2 ≤ B*M := by dsimp [B]; nlinarith
  have hp1 : B^(e+1) ≤ B^(2*e+1) := pow_le_pow_right₀ hB (by omega)
  have hp2 : B^(e+2) ≤ B^(2*e+1) := pow_le_pow_right₀ hB (by omega)
  change B^e*S ≤ T+B^(e+2)*M at hinter
  change _ ≤ 3*6^e*(T+B^(2*e+1)*M)
  by_cases hsmall : M ≤ 1
  · have hbase : 1+P^2 ≤ 6*B := by
      have hsq : M^2 ≤ M := by nlinarith
      dsimp [B]
      nlinarith
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+P^2) hbase e
    have hb : B^e*(S+2*M^2) ≤ T+3*(B^(2*e+1)*M) := by
      have hx := mul_le_mul_of_nonneg_left hM2 (pow_nonneg hB0 e)
      have hp1m := mul_le_mul_of_nonneg_right hp1 hM
      have hp2m := mul_le_mul_of_nonneg_right hp2 hM
      rw [pow_succ] at hp1m
      nlinarith
    calc
      _ ≤ (6*B)^e*(S+2*M^2) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = 6^e*(B^e*(S+2*M^2)) := by rw [mul_pow,mul_assoc]
      _ ≤ 6^e*(T+3*(B^(2*e+1)*M)) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ (6:ℝ)^e) hT]
  · have hlarge : 1 ≤ M := le_of_not_ge hsmall
    have hbase : 1+P^2 ≤ 6*B^2 := by dsimp [B]; nlinarith [sq_nonneg (S-M)]
    have henergy : S+2*M^2 ≤ 3*B*M := by
      have hSM := mul_le_mul_of_nonneg_left hlarge hS
      dsimp [B] at *
      nlinarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+P^2) hbase e
    calc
      _ ≤ (6*B^2)^e*(3*B*M) := mul_le_mul hp henergy (by positivity) (by positivity)
      _ = 3*6^e*(B^(2*e+1)*M) := by rw [mul_pow,← pow_mul,pow_succ]; ring
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left hT

end NLS.ZakharovShabat
