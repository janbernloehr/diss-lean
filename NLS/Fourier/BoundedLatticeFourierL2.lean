import NLS.Fourier.PerturbedLatticeMomentIntegral

/-! # L2 sampling at bounded complex lattice displacements

The norm-convergent moment series realizes the actual Fourier samples. The displacement sequence need only be bounded.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- Actual Fourier samples at any bounded complex displacement of the pi
lattice have an L2 realization with an exponential operator bound.
The displacement sequence need not itself be square summable. -/
theorem exists_bounded_lattice_fourier_coefficients
    (f : ℝ → ℂ) (hf : Continuous f) (δ : NLS.Coeff ⊤) :
    ∃ a : NLS.Coeff 2,
      (∀ n, a n = ∫ x in (0:ℝ)..1, f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x)) ∧
      ‖a‖ ≤ Real.exp (2*‖δ‖)*
        ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖ := by
  obtain ⟨hs,hn⟩ := summable_boundedLatticeMomentTerm f hf δ
  refine ⟨∑' k, boundedLatticeMomentTerm f hf δ k,?_,hn⟩
  intro n
  have hc := (lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) 2 n).hasSum hs.of_norm.hasSum
  change HasSum (fun k => boundedLatticeMomentTerm f hf δ k n)
    ((∑' k, boundedLatticeMomentTerm f hf δ k) n) at hc
  simp only [boundedLatticeMomentTerm_apply] at hc
  exact hc.unique (hasSum_perturbed_lattice_moment_integrals f hf n (δ n))

end NLS.Fourier
