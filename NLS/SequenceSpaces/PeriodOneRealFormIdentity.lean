import NLS.SequenceSpaces.PeriodOneRealScaling
import NLS.ComplexAnalysis.ContinuousRealFormIdentity

/-! # Physical real-form uniqueness in the complex rough potential space

Actual conjugate Fourier reflection is continuous and antilinear. Its
fixed real and imaginary parts give a continuous complexification. The
canonical connected real-form identity theorem then applies.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS

/-- Physical conjugation preserves addition. -/
theorem periodOneHminusConjugation_add (a b : PeriodOneHminusOne) :
    periodOneHminusConjugation (a+b) = periodOneHminusConjugation a+periodOneHminusConjugation b := by
  apply Subtype.ext
  funext k
  rw [periodOneHminusConjugation_apply]
  change conj (a.val (-k)+b.val (-k)) = (periodOneHminusConjugation a).val k+(periodOneHminusConjugation b).val k
  rw [map_add,periodOneHminusConjugation_apply,periodOneHminusConjugation_apply]

/-- Physical conjugation conjugates a complex scalar. -/
theorem periodOneHminusConjugation_smul (z : ℂ) (q : PeriodOneHminusOne) :
    periodOneHminusConjugation (z • q) = conj z • periodOneHminusConjugation q := by
  apply Subtype.ext
  funext k
  rw [periodOneHminusConjugation_apply]
  change conj (z*q.val (-k)) = conj z*(periodOneHminusConjugation q).val k
  rw [map_mul,periodOneHminusConjugation_apply]

/-- Physical conjugation is continuous in the actual rough-potential norm. -/
theorem continuous_periodOneHminusConjugation : Continuous periodOneHminusConjugation := by
  change Continuous (fun q : PeriodOneHminusOne =>
    (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm
      (star (Coeff.reflection (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2 q))))
  exact (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm.continuous.comp
    (continuous_star.comp (Coeff.reflection.continuous.comp
      (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).continuous))

/-- Physical conjugation preserves subtraction. -/
theorem periodOneHminusConjugation_sub (a b : PeriodOneHminusOne) :
    periodOneHminusConjugation (a-b) = periodOneHminusConjugation a-periodOneHminusConjugation b := by
  apply Subtype.ext
  funext k
  rw [periodOneHminusConjugation_apply]
  change conj (a.val (-k)-b.val (-k)) = (periodOneHminusConjugation a).val k-(periodOneHminusConjugation b).val k
  rw [map_sub,periodOneHminusConjugation_apply,periodOneHminusConjugation_apply]

/-- The physical real part of a rough Fourier potential. -/
def periodOneHminusRealPart (q : PeriodOneHminusOne) := (1/2 : ℂ) • (q+periodOneHminusConjugation q)
/-- The physical imaginary part of a rough Fourier potential. -/
def periodOneHminusImagPart (q : PeriodOneHminusOne) := (-I/2 : ℂ) • (q-periodOneHminusConjugation q)

/-- The physical real part is fixed by conjugation. -/
theorem periodOneHminusRealPart_isReal (q : PeriodOneHminusOne) :
    periodOneHminusConjugation (periodOneHminusRealPart q) = periodOneHminusRealPart q := by
  unfold periodOneHminusRealPart
  rw [periodOneHminusConjugation_smul,periodOneHminusConjugation_add,periodOneHminusConjugation_involutive]
  have hz : conj (1/2 : ℂ) = (1/2 : ℂ) := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; rfl,conj_ofReal]
  rw [hz,add_comm]

/-- The physical imaginary part is fixed by conjugation. -/
theorem periodOneHminusImagPart_isReal (q : PeriodOneHminusOne) :
    periodOneHminusConjugation (periodOneHminusImagPart q) = periodOneHminusImagPart q := by
  unfold periodOneHminusImagPart
  rw [periodOneHminusConjugation_smul,periodOneHminusConjugation_sub,periodOneHminusConjugation_involutive]
  have hz : conj (-I/2 : ℂ) = I/2 := by
    rw [map_div₀,map_neg,conj_I,neg_neg,show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,conj_ofReal]
  rw [hz,show periodOneHminusConjugation q-q = -(q-periodOneHminusConjugation q) by abel,
    smul_neg,← neg_smul]
  congr 1
  ring

/-- The physical real and imaginary parts reconstruct every complex rough potential. -/
theorem periodOneHminusRealPart_add_I_smul_imag (q : PeriodOneHminusOne) : q = periodOneHminusRealPart q+I • periodOneHminusImagPart q := by
  unfold periodOneHminusRealPart periodOneHminusImagPart
  rw [smul_smul]
  have he : (I : ℂ)*(-I/2) = 1/2 := by rw [mul_div,mul_neg,I_mul_I,neg_neg]
  rw [he,← smul_add]
  have hsum : q+periodOneHminusConjugation q+(q-periodOneHminusConjugation q) = (2 : ℂ) • q := by module
  rw [hsum,smul_smul]
  norm_num

/-- Agreement on the physical real slice determines analytic functions on a connected open domain containing zero. -/
theorem periodOneHminus_real_form_identity {U : Set PeriodOneHminusOne}
    (hU : IsOpen U) (hconn : IsPreconnected U) (h0U : (0 : PeriodOneHminusOne) ∈ U)
    (F G : PeriodOneHminusOne → ℂ) (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (he : ∀ q ∈ U, periodOneHminusConjugation q = q → F q = G q) : EqOn F G U := by
  let R : Set PeriodOneHminusOne := {q | periodOneHminusConjugation q = q}
  have hRadd : ∀ {x y : PeriodOneHminusOne}, x ∈ R → y ∈ R → x+y ∈ R := by
    intro x y hx hy
    change periodOneHminusConjugation (x+y) = x+y
    rw [periodOneHminusConjugation_add,hx,hy]
  have hRsmul : ∀ t : ℝ, ∀ {x : PeriodOneHminusOne}, x ∈ R → (t : ℂ) • x ∈ R := by
    intro t x hx
    change periodOneHminusConjugation ((t : ℂ) • x) = (t : ℂ) • x
    rw [periodOneHminusConjugation_smul,conj_ofReal,hx]
  have hA : Continuous periodOneHminusRealPart := (continuous_id.add continuous_periodOneHminusConjugation).const_smul (1/2 : ℂ)
  have hB : Continuous periodOneHminusImagPart := (continuous_id.sub continuous_periodOneHminusConjugation).const_smul (-I/2 : ℂ)
  have hA0 : periodOneHminusRealPart 0 = 0 := by simp [periodOneHminusRealPart]
  have hB0 : periodOneHminusImagPart 0 = 0 := by simp [periodOneHminusImagPart]
  have hz := AnalyticOnNhd.eqOn_zero_of_continuous_real_form R (fun {_ _} hx hy => hRadd hx hy) (fun t {_} hx => hRsmul t hx) periodOneHminusRealPart periodOneHminusImagPart
    periodOneHminusRealPart_isReal periodOneHminusImagPart_isReal periodOneHminusRealPart_add_I_smul_imag hA.continuousAt hA0 hB.continuousAt hB0
    U hU hconn ⟨0,h0U,periodOneHminusConjugation_zero⟩ (F-G) (hF.sub hG)
    (fun q hq hqr => sub_eq_zero.mpr (he q hq hqr))
  intro q hq
  exact sub_eq_zero.mp (hz hq)

end NLS
