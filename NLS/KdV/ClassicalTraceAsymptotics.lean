import NLS.KdV.RiccatiEnergy
import NLS.KdV.ConstantUpperSpectralBridge
import NLS.ZakharovShabat.NLSHamiltonianDiscriminantAsymptotics

/-! # Physical KdV coefficients in the actual scalar Hill trace

The all-order discriminant estimate from the existing NLS library applies
to the constant-upper potential (-1,-q). The actual scalar Hill solutions
and their normalized trace were constructed in the bridge module. The
first five phase coefficients are calculated from the actual KdV energy,
rather than being spectral hypotheses of the theorem below.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

/-- Restrict the original scalar potential to one period, without a change
of coordinates or norm in its values. -/
def scalarPotentialCurve (q : ℝ → ℂ) (hq : Continuous q) : NLS.LinearVolterra.Curve ℂ :=
  ⟨fun t => q t, hq.comp continuous_subtype_val⟩

theorem constantUpperPotential_scalarPotentialCurve (q : ℝ → ℂ) (hq : Continuous q) :
    constantUpperPotential (scalarPotentialCurve q hq) =
      classicalPotentialOfFunctions (fun _ => -1) (-q) continuous_const hq.neg := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- The fifth-order physical phase has exactly the KdV coefficients
z-H_0/(4*z^3)-Hkdv/(16*z^5), with spectral energy lambda=z^2. -/
theorem phase_const_upper_five (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) (hmean : (∫ x in (0 : ℝ)..1, q x) = 0)
    (z : ℂ) (hz : z ≠ 0) :
    I * nlsHamiltonianPhase (fun _ => -1) (-q) 5 z =
      z - classicalQuadraticInvariant q / (4 * z ^ 3) - classicalHamiltonian q / (16 * z ^ 5) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := classicalNLSHamiltonian_const_upper_first_five q hq hp hmean
  simp [nlsHamiltonianPhase, Finset.sum_range_succ, h1, h2, h3, h4, h5]
  field_simp
  ring_nf
  simp [I_sq]
  ring

/-- All higher orders retain the physical first five coefficients and
an explicit tail of the already constructed NLS Hamiltonians. -/
theorem phase_const_upper_extended (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) (hmean : (∫ x in (0 : ℝ)..1, q x) = 0)
    (N : ℕ) (z : ℂ) (hz : z ≠ 0) :
    I * nlsHamiltonianPhase (fun _ => -1) (-q) (N+5) z =
      z - classicalQuadraticInvariant q / (4 * z ^ 3) - classicalHamiltonian q / (16 * z ^ 5) -
        ∑ j ∈ Finset.range N, classicalNLSHamiltonian (fun _ => -1) (-q) (j+6) / (2*z) ^ (j+6) := by
  have hsplit : nlsHamiltonianPhase (fun _ => -1) (-q) (N+5) z =
      nlsHamiltonianPhase (fun _ => -1) (-q) 5 z +
        ∑ j ∈ Finset.range N, I * classicalNLSHamiltonian (fun _ => -1) (-q) (j+6) / (2*z) ^ (j+6) := by
    unfold nlsHamiltonianPhase
    rw [show N+5 = 5+N by omega, Finset.sum_range_add]
    have hidx (j : ℕ) : 5+j+1 = j+6 := by omega
    simp_rw [hidx]
    ring
  have htail : I * (∑ j ∈ Finset.range N,
      I * classicalNLSHamiltonian (fun _ => -1) (-q) (j+6) / (2*z) ^ (j+6)) =
      -(∑ j ∈ Finset.range N,
        classicalNLSHamiltonian (fun _ => -1) (-q) (j+6) / (2*z) ^ (j+6)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_div_assoc, ← mul_assoc, I_mul_I, neg_one_mul, neg_div]
  rw [hsplit, mul_add, phase_const_upper_five q hq hp hmean z hz, htail]
  ring

/-- All-order asymptotics of the actual scalar trace. Higher coefficients
are retained explicitly, so the fifth energy coefficient is not inferred
from an error term of the same order. -/
theorem exists_constantUpperHillTrace_higher_error_bound (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (hmean : (∫ x in (0 : ℝ)..1, q x) = 0) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ |r| →
      ‖constantUpperHillTrace (scalarPotentialCurve q hq.continuous) r -
        2 * cos ((r : ℂ) - classicalQuadraticInvariant q / (4 * (r : ℂ) ^ 3) -
          classicalHamiltonian q / (16 * (r : ℂ) ^ 5) -
          ∑ j ∈ Finset.range N, classicalNLSHamiltonian (fun _ => -1) (-q) (j+6) /
            (2*(r : ℂ)) ^ (j+6))‖ ≤ C / (2 * |r|) ^ (N+5) := by
  obtain ⟨C,hC,herr⟩ := exists_classicalDiscriminant_hamiltonian_error_bound
    (fun _ => -1) (-q) contDiff_const hq.neg (fun _ => rfl)
    (fun x => by change -q (x+1) = -q x; rw [hp x]) (N+5)
  refine ⟨C,hC,?_⟩
  intro r hr
  have hr0 : r ≠ 0 := by
    intro he
    simp only [he, abs_zero] at hr
    norm_num at hr
  have h := herr r hr
  rw [phase_const_upper_extended q hq hp hmean N r (ofReal_ne_zero.mpr hr0)] at h
  rw [constantUpperHillTrace_eq_discriminant,
    constantUpperPotential_scalarPotentialCurve]
  exact h

/-- The actual normalized scalar Hill trace has the physical KdV
Hamiltonian asymptotics on the real spectral axis. The error bound holds
for every |r|>=1, for each fixed smooth periodic mean-zero q. -/
theorem exists_constantUpperHillTrace_energy_error_bound (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (hmean : (∫ x in (0 : ℝ)..1, q x) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ |r| →
      ‖constantUpperHillTrace (scalarPotentialCurve q hq.continuous) r -
        2 * cos ((r : ℂ) - classicalQuadraticInvariant q / (4 * (r : ℂ) ^ 3) -
          classicalHamiltonian q / (16 * (r : ℂ) ^ 5))‖ ≤ C / (2 * |r|) ^ 5 := by
  simpa using exists_constantUpperHillTrace_higher_error_bound q hq hp hmean 0

end NLS.KdV
