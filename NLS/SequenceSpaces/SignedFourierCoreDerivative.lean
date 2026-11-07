import NLS.ComplexAnalysis.LinearObservationsDerivative
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.SequenceSpaces.PositiveFourierInverseMajorant

/-! The ENTIRE signed native Fourier core equals its ACTUAL derivative
at zero, with the SAME source inclusion, coefficients and fixed signs. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem signed_fourier_core_eq_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v w : Weight) (L : E →L[ℂ] WeightedCoeff v 2)
    (U : Set E) (hU : IsOpen U) (h0 : (0:E)∈U)
    (A : E → WeightedCoeff w 2) (DA : E →L[ℂ] WeightedCoeff w 2)
    (hAd : HasFDerivAt A DA 0) (e : ℤ → Bool) (c : ℕ+ → ℂ)
    (hc : ∀ q∈U,(A q).val 0=0 ∧ ∀ n : ℕ+,
      (A q).val (n:ℤ)=(if e (n:ℤ) then -(c n*(L q).val (n:ℤ)) else c n*(L q).val (n:ℤ)) ∧
      (A q).val (-(n:ℤ))=(if e (n:ℤ) then -(c n*(L q).val (-(n:ℤ))) else c n*(L q).val (-(n:ℤ)))) :
    ∀ q∈U,A q=DA q := by
  apply NLS.ComplexAnalysis.eq_derivative_of_linear_observations U hU h0 A DA hAd (evalCLM w 2)
  · intro x y hxy
    apply Subtype.ext
    funext j
    exact hxy j
  intro j
  by_cases hj0 : j=0
  · subst j
    exact ⟨0,fun q hq => (hc q hq).1⟩
  by_cases hj : 0<j
  · let n := Coeff.positivePoleIndex j hj
    have hn : (n:ℤ)=j := by exact_mod_cast Coeff.positivePoleIndex_real j hj
    let C := ((if e (n:ℤ) then -c n else c n):ℂ) • ((evalCLM v 2 j).comp L)
    refine ⟨C,?_⟩
    intro q hq
    change (A q).val j=(if e (n:ℤ) then -c n else c n)*(L q).val j
    rw [←hn,((hc q hq).2 n).1]
    cases e (n:ℤ) <;> simp only [Bool.false_eq_true,↓reduceIte,neg_mul]
  · have hjneg : 0< -j := by omega
    let n := Coeff.positivePoleIndex (-j) hjneg
    have hn : (n:ℤ)= -j := by exact_mod_cast Coeff.positivePoleIndex_real (-j) hjneg
    have hnj : -(n:ℤ)=j := by omega
    let C := ((if e (n:ℤ) then -c n else c n):ℂ) • ((evalCLM v 2 j).comp L)
    refine ⟨C,?_⟩
    intro q hq
    have h := ((hc q hq).2 n).2
    change (A q).val j=(if e (n:ℤ) then -c n else c n)*(L q).val j
    rw [←hnj,h]
    cases e (n:ℤ) <;> simp only [Bool.false_eq_true,↓reduceIte,neg_mul]

end NLS.WeightedCoeff
