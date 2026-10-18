import NLS.Fourier.BoundedLatticeFourierL2
import NLS.Fourier.BoundedLatticeDifferenceSeries

/-! # Exact factorization of the Fourier sampling error

The actual sampling error factors by the displacement and an L2 divided difference. At zero displacement the value is the exact spectral derivative.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- The actual Fourier sampling difference factors by the displacement
through an L2 sequence with uniform norm bound. At zero displacement the
same sequence has the exact removable derivative value. -/
theorem exists_bounded_lattice_fourier_difference
    (f : ℝ → ℂ) (hf : Continuous f) (δ : NLS.Coeff ⊤) :
    ∃ r : NLS.Coeff 2,
      (∀ n, (∫ x in (0:ℝ)..1, f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x))-
        periodOneCoefficient f n = δ n*r n) ∧
      (∀ n, δ n = 0 → r n = -2*I*periodOneCoefficient (fun x => (x:ℂ)*f x) n) ∧
      ‖r‖ ≤ (2*Real.exp (2*‖δ‖))*
        ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖ := by
  obtain ⟨hs,hn⟩ := summable_boundedLatticeDifferenceTerm f hf δ
  let r : NLS.Coeff 2 := ∑' k, boundedLatticeDifferenceTerm f hf δ k
  have hc (n : ℤ) : HasSum (fun k => boundedLatticeDifferenceTerm f hf δ k n) (r n) := by
    exact (lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) 2 n).hasSum hs.of_norm.hasSum
  refine ⟨r,?_,?_,hn⟩
  · intro n
    have hshift := (hasSum_nat_add_iff' 1).mpr
      (hasSum_perturbed_lattice_moment_integrals f hf n (δ n))
    simp only [Finset.sum_range_one,pow_zero,Nat.factorial_zero,Nat.cast_one,
      div_one,one_mul] at hshift
    have hm := (hc n).mul_left (δ n)
    have he (k : ℕ) : δ n*boundedLatticeDifferenceTerm f hf δ k n =
        ((-2*I*δ n)^(k+1)/((k+1).factorial:ℂ))*
          periodOneCoefficient (fun x => (x:ℂ)^(k+1)*f x) n := by
      simp only [boundedLatticeDifferenceTerm_apply,mul_pow,pow_succ]
      ring
    simp only [he] at hm
    exact hshift.unique hm
  · intro n hδ
    have hz (k : ℕ) (hk : k ≠ 0) : boundedLatticeDifferenceTerm f hf δ k n = 0 := by
      simp [boundedLatticeDifferenceTerm_apply,hδ,zero_pow hk]
    rw [← (hc n).tsum_eq,tsum_eq_single 0 hz]
    simp [boundedLatticeDifferenceTerm_apply]

end NLS.Fourier
