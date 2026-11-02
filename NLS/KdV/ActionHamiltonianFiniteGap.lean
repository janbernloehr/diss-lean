import NLS.KdV.ActionHamiltonianTrace
import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition

/-! # Finite-gap contour decomposition of the KdV Hamiltonian

Equations (4.11)–(4.12) of arXiv:1502.05857v1 follow from the shared
finite-hole Cauchy theorem and the proved quartic gap-period calculation.
The theorem concerns the actual exterior contour coefficient of the
quartic primitive. Its identity with physical energy still requires the
KdV high-energy expansion (4.7).
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

/-- A finite sum of quartic gap periods is exactly the sum of its linear
action terms and cubic contour moments, retaining the source coefficients. -/
theorem sum_quartic_gap_contributions
    (A : Finset ℕ+) (F : ℕ+ → ℂ → ℂ) (c : ℕ+ → ℂ) (r : ℕ+ → ℝ)
    (hr : ∀ n ∈ A, 0 ≤ r n)
    (hcont : ∀ n ∈ A, ContinuousOn (F n) (sphere (c n) (r n)))
    (hF : ∀ n ∈ A, AnalyticOnNhd ℂ (fun z => F n z ^ 2) (closedBall (c n) (r n))) :
    (∑ n ∈ A, (-4 : ℂ) * (2 * Real.pi * I : ℂ)⁻¹ *
      (∮ z in C(c n,r n), (F n z - I * (n : ℂ) * Real.pi) ^ 4)) =
      (∑ n ∈ A, ((8 * (n : ℝ) ^ 3 * Real.pi ^ 3 : ℝ) : ℂ) *
        primitiveAction (F n) (c n) (r n)) +
      ∑ n ∈ A, ((8 * (n : ℝ) * Real.pi : ℝ) : ℂ) * cubicMoment (F n) (c n) (r n) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact quartic_gap_contribution (F n) (c n) (r n) (n : ℝ)
    (hr n hn) (hcont n hn) (hF n hn)

/-- The exterior quartic period decomposes into physical-normalization
action periods and nonlinear cubic moments on finitely many isolating
circles. All periods have counterclockwise orientation.

Analyticity on the perforated disc and analytic local squares are the
actual analytic hypotheses. No contour deformation equality, energy
trace formula, or conclusion is supplied as an assumption. -/
theorem finite_gap_contour_identity
    (d : ℂ) (S : ℝ) (hS : 0 ≤ S) (A : Finset ℕ+)
    (c : ℕ+ → ℂ) (r R : ℕ+ → ℝ) (Q : ℂ → ℂ) (F : ℕ+ → ℂ → ℂ)
    (hr : ∀ n ∈ A, 0 < r n) (hrR : ∀ n ∈ A, r n < R n)
    (henclosed : ∀ n ∈ A, closedBall (c n) (R n) ⊆ ball d S)
    (hdisj : ∀ n ∈ A, ∀ m ∈ A, n ≠ m →
      Disjoint (closedBall (c n) (R n)) (closedBall (c m) (R m)))
    (hQ : AnalyticOnNhd ℂ Q (ComplexAnalysis.circleHoleDomain d S A c r))
    (hcont : ∀ n ∈ A, ContinuousOn (F n) (sphere (c n) (r n)))
    (hsquare : ∀ n ∈ A, AnalyticOnNhd ℂ (fun z => F n z ^ 2) (closedBall (c n) (r n)))
    (hmatch : ∀ n ∈ A, ∀ z ∈ sphere (c n) (r n),
      Q z = (F n z - I * (n : ℂ) * Real.pi) ^ 4) :
    (-4 : ℂ) * (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(d,S), Q z) =
      (∑ n ∈ A, ((8 * (n : ℝ) ^ 3 * Real.pi ^ 3 : ℝ) : ℂ) *
        primitiveAction (F n) (c n) (r n)) +
      ∑ n ∈ A, ((8 * (n : ℝ) * Real.pi : ℝ) : ℂ) * cubicMoment (F n) (c n) (r n) := by
  rw [ComplexAnalysis.circleIntegral_eq_sum_of_finite_holes d S hS A c r R Q
    hr hrR henclosed hdisj hQ, Finset.mul_sum]
  have hperiod (n : ℕ+) (hn : n ∈ A) : (∮ z in C(c n,r n), Q z) =
      ∮ z in C(c n,r n), (F n z - I * (n : ℂ) * Real.pi) ^ 4 :=
    circleIntegral.integral_congr (hr n hn).le (hmatch n hn)
  simp_rw [Finset.sum_congr rfl (fun n hn => congrArg
    (fun t : ℂ => (-4 : ℂ) * (2 * Real.pi * I : ℂ)⁻¹ * t) (hperiod n hn))]
  exact sum_quartic_gap_contributions A F c r (fun n hn => (hr n hn).le) hcont hsquare

end NLS.KdV
