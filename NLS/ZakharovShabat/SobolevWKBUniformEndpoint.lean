import NLS.ZakharovShabat.SobolevWKBUniformComparison
import NLS.ZakharovShabat.NLSHamiltonianPhasePolynomial

/-! # Uniform Sobolev WKB endpoint comparison

The actual monodromy has a Hamiltonian approximate eigenvector uniformly on each Hs ball and spectral strip.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The Hamiltonian approximate eigenvector error is uniform on the original
Hs ball at every truncation order N <= s and every fixed spectral strip. -/
theorem exists_uniform_nlsWKBVector_strip_endpoint_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
        ‖classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z
            (nlsWKBVector a b N z 0) 1-
          exp (nlsHamiltonianPhase a b N z) • nlsWKBVector a b N z 0‖ ≤ C/(2*‖z‖)^N := by
  obtain ⟨C,hC,h⟩ := exists_uniform_nlsWKBVector_strip_solution_error_bound s N hs hNs R hR H
  refine ⟨C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hzn hzH
  have he := h ab hab a b ha hb hpa hpb hca hcb z hzn hzH ⟨1,⟨zero_le_one,le_rfl⟩⟩
  rw [norm_sub_rev,nlsWKBVector_one a b ha hb hpa hpb] at he
  exact he

end NLS.ZakharovShabat
