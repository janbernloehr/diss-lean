import NLS.Fourier.MemLpLatticeMomentSeries
import NLS.Fourier.PerturbedLatticeIntegrableMoments

/-! # Bounded complex Fourier sampling of arbitrary L2 data

Actual samples at a bounded complex perturbation of the pi lattice have an L2 realization with the exponential operator bound.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- Actual Fourier samples at any bounded complex displacement of the pi
lattice have an L2 realization with an exponential operator bound.
The displacement sequence need not itself be square summable. -/
theorem exists_memLp_bounded_lattice_fourier_coefficients
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (δ : NLS.Coeff ⊤) :
    ∃ a : NLS.Coeff 2,
      (∀ n, a n = ∫ x in (0:ℝ)..1, f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x)) ∧
      ‖a‖ ≤ Real.exp (2*‖δ‖)*
        ‖unitIntervalMemLpCoefficients f hf‖ := by
  obtain ⟨hs,hn⟩ := summable_memLpLatticeMomentTerm f hf δ
  refine ⟨∑' k, memLpLatticeMomentTerm f hf δ k,?_,hn⟩
  intro n
  have hc := (lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) 2 n).hasSum hs.of_norm.hasSum
  change HasSum (fun k => memLpLatticeMomentTerm f hf δ k n)
    ((∑' k, memLpLatticeMomentTerm f hf δ k) n) at hc
  simp only [memLpLatticeMomentTerm_apply] at hc
  exact hc.unique (hasSum_integrable_perturbed_lattice_moments f (hf.integrable (by norm_num)) n (δ n))

end NLS.Fourier
