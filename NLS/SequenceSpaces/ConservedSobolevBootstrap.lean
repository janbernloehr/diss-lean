import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
namespace NLS.SequenceSpaces

/-- The exact exponent m^2+m-1 in the dynamical corollary. The lower target
bound is kept separate so that its conservation must be established by the
actual evolution, rather than assumed as part of a replacement Birkhoff map. -/
theorem conservedSobolev_bootstrap (m : ℕ) (hm : 1 ≤ m)
    (P Q S T U c d b : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hT : 0 ≤ T)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hS : S ≤ c*(P+(1+Q)^m*Q))
    (hB : T ≤ b*(1+Q)^(m-1)*Q)
    (hU : U ≤ d*(S+(1+T)^m*T)) :
    U ≤ d*(c+(1+b)^m*b)*(P+(1+Q)^(m*m+m-1)*Q) := by
  let X := 1+Q
  have hX : 1 ≤ X := by dsimp [X]; linarith
  have hX0 : 0 ≤ X := by linarith
  have hQX : Q ≤ X := by dsimp [X]; linarith
  have hm1 : m-1+1 = m := by omega
  have hBX : T ≤ b*X^m := by
    apply hB.trans
    change b*X^(m-1)*Q ≤ _
    calc
      _ ≤ b*X^(m-1)*X := mul_le_mul_of_nonneg_left hQX (by positivity)
      _ = _ := by rw [mul_assoc,← pow_succ,hm1]
  have h1 : 1+T ≤ (1+b)*X^m := by
    have hx := one_le_pow₀ hX (n := m)
    nlinarith
  have hTm : (1+T)^m ≤ (1+b)^m*X^(m*m) := by
    apply (pow_le_pow_left₀ (by linarith) h1 m).trans_eq
    rw [mul_pow,← pow_mul]
  have he : m*m+(m-1) = m*m+m-1 := by omega
  have hTT : (1+T)^m*T ≤ (1+b)^m*b*X^(m*m+m-1)*Q := by
    apply (mul_le_mul hTm hB hT (by positivity)).trans_eq
    change ((1+b)^m*X^(m*m))*(b*X^(m-1)*Q) = _
    rw [show (1+b)^m*X^(m*m)*(b*X^(m-1)*Q) =
      (1+b)^m*b*(X^(m*m)*X^(m-1))*Q by ring,← pow_add,he]
  have hmE : m ≤ m*m+m-1 := by
    have : 1 ≤ m*m := Nat.mul_pos hm hm
    omega
  have hlow : X^m*Q ≤ X^(m*m+m-1)*Q :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hX hmE) hQ
  have hinner : S+(1+T)^m*T ≤ (c+(1+b)^m*b)*(P+X^(m*m+m-1)*Q) := by
    change S ≤ c*(P+X^m*Q) at hS
    have hSc := hS.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hlow) hc)
    nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ (1+b)^m) hb) hP]
  exact hU.trans (by simpa only [X,mul_assoc] using mul_le_mul_of_nonneg_left hinner hd)

end NLS.SequenceSpaces
