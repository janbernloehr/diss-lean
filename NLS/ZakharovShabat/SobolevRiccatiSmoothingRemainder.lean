import NLS.ZakharovShabat.SobolevRiccatiHierarchy

/-! # Additional regularity of the nonlinear Riccati remainder

Removing the leading Fourier derivative leaves a canonical analytic remainder with one additional Sobolev derivative, through the top density.
-/

noncomputable section
open Complex
namespace NLS.ZakharovShabat

/-- Removing the leading derivative leaves one additional Sobolev order.
The definition uses the actual lower Riccati densities and convolutions. -/
def sobolevRiccatiSmoothingRemainder (s : ℕ) (ab : SobolevSource s) :
    (n : ℕ) → n ≤ s → ScalarSobolev (s-n+1)
  | 0, _ => 0
  | 1, _ => 0
  | n+2, hn =>
      hierarchySobolevDerivative (s-(n+1)+1) (s-(n+2)+1) (by omega)
        (sobolevRiccatiSmoothingRemainder s ab (n+1) (by omega)) +
      ∑ ij ∈ (Finset.antidiagonal n).attach,
        hierarchySobolevTriple (s-(n+2)+1)
          (hierarchySobolevInclusion s (s-(n+2)+1+1) (by omega) ab.1)
          (hierarchySobolevInclusion (s-ij.val.1) (s-(n+2)+1+1)
            (by have he := Finset.mem_antidiagonal.mp ij.property; omega)
            (sobolevRiccatiDensity s ab ij.val.1
              (by have he := Finset.mem_antidiagonal.mp ij.property; omega)))
          (hierarchySobolevInclusion (s-ij.val.2) (s-(n+2)+1+1)
            (by have he := Finset.mem_antidiagonal.mp ij.property; omega)
            (sobolevRiccatiDensity s ab ij.val.2
              (by have he := Finset.mem_antidiagonal.mp ij.property; omega)))
termination_by n => n

private theorem smoothing_sum_val {ι : Type*} (s : ℕ) (S : Finset ι)
    (f : ι → ScalarSobolev s) (j : ℤ) :
    (∑ i ∈ S, f i).val j = ∑ i ∈ S, (f i).val j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,WeightedCoeff.zero_val]
  | @insert a S ha ih => simp only [Finset.sum_insert ha,WeightedCoeff.add_val,ih]

/-- The additional-regularity remainder is the literal original density
plus the leading period-one derivative at every Fourier coefficient. -/
theorem sobolevRiccatiSmoothingRemainder_apply (s n : ℕ) (hn : n ≤ s)
    (ab : SobolevSource s) (j : ℤ) :
    (sobolevRiccatiSmoothingRemainder s ab n hn).val j =
      (sobolevRiccatiDensity s ab n hn).val j+(2*I*(Real.pi:ℂ)*j)^n*ab.2.val j := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [sobolevRiccatiSmoothingRemainder]
    · simp [sobolevRiccatiSmoothingRemainder,sobolevRiccatiDensity_one]
    · rw [sobolevRiccatiSmoothingRemainder,sobolevRiccatiDensity_succ_succ]
      simp only [WeightedCoeff.add_val,hierarchySobolevDerivative_apply,smoothing_sum_val,
        hierarchySobolevTriple_apply,hierarchySobolevInclusion_apply]
      rw [ih (n+1) (by omega) (by omega)]
      ring

/-- The gain of one Sobolev order is analytic on the original complex
source space, including the top density n=s. -/
theorem analyticAt_sobolevRiccatiSmoothingRemainder (s n : ℕ) (hn : n ≤ s)
    (ab : SobolevSource s) :
    AnalyticAt ℂ (fun cd => sobolevRiccatiSmoothingRemainder s cd n hn) ab := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa only [sobolevRiccatiSmoothingRemainder] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : SobolevSource s => (0 : ScalarSobolev (s-0+1))) ab)
    · have he : (fun cd : SobolevSource s => sobolevRiccatiSmoothingRemainder s cd (0+1) hn) =
          (fun _ => (0 : ScalarSobolev (s-1+1))) := by
        funext cd
        rw [sobolevRiccatiSmoothingRemainder]
      rw [he]
      exact analyticAt_const
    · simp only [sobolevRiccatiSmoothingRemainder]
      apply AnalyticAt.add
      · exact ((hierarchySobolevDerivative (s-(n+1)+1) (s-(n+2)+1) (by omega)).analyticAt _).comp
          (ih (n+1) (by omega) (by omega))
      · apply Finset.analyticAt_fun_sum
        intro ij _
        have he := Finset.mem_antidiagonal.mp ij.property
        apply analyticAt_hierarchySobolevTriple
        · exact ((hierarchySobolevInclusion s (s-(n+2)+1+1) (by omega)).analyticAt ab.1).comp
            ((ContinuousLinearMap.fst ℂ (ScalarSobolev s) (ScalarSobolev s)).analyticAt ab)
        · exact ((hierarchySobolevInclusion (s-ij.val.1) (s-(n+2)+1+1) (by omega)).analyticAt _).comp
            (analyticAt_sobolevRiccatiDensity s ij.val.1 (by omega) ab)
        · exact ((hierarchySobolevInclusion (s-ij.val.2) (s-(n+2)+1+1) (by omega)).analyticAt _).comp
            (analyticAt_sobolevRiccatiDensity s ij.val.2 (by omega) ab)

end NLS.ZakharovShabat
