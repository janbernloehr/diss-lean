import NLS.ZakharovShabat.SourceSection16Original
import NLS.ZakharovShabat.SourceBirkhoffJacobianRange

/-!
# Canonical directions under the original normalized Jacobian

The x Hamiltonian maps to a y output mode and the y Hamiltonian maps to
a negative x mode. The exact Fourier inverse therefore gives negative
y and x gradients, respectively. This corrects the unswapped indices
in the first display of the proof of Proposition 17.1.
-/

noncomputable section
open Set Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection16OriginalData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Exact signed images of the Hamiltonians of actual coordinate derivatives. -/
theorem jacobian_hamiltonian_coordinates (D : SourceSection16OriginalData hp hp1 W₀ W V s)
    (h2p : 2 ≤ p) (φ : realTypeSourceSubmodule p) (m : ℤ) :
    sourceBirkhoffJacobian hp hp1 s φ.val
      (sourceHamiltonianDirection h2p (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 m) φ.val)) =
        (0,lp.single p m 1) ∧
    sourceBirkhoffJacobian hp hp1 s φ.val
      (sourceHamiltonianDirection h2p (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 m) φ.val)) =
        -(lp.single p m 1,0) := by
  have hφ := D.complex.real_subset φ.property
  constructor
  · apply Prod.ext <;> ext n
    · rw [(D.complex.jacobian_coordinates φ.val hφ _ n).1,
        ← (D.complex.fderiv_coordinates n φ.val hφ).1,apply_sourceHamiltonianDirection]
      exact (D.complex.sourceBracket_canonical h2p n m φ).1
    · rw [(D.complex.jacobian_coordinates φ.val hφ _ n).2,
        ← (D.complex.fderiv_coordinates n φ.val hφ).2,apply_sourceHamiltonianDirection,
        sourceBivector_antisymm]
      change -sourceBracket h2p _ _ φ.val = _
      rw [(D.complex.sourceBracket_canonical h2p m n φ).2.1]
      simp [lp.single_apply,Pi.single_apply,eq_comm]
  · apply Prod.ext <;> ext n
    · rw [(D.complex.jacobian_coordinates φ.val hφ _ n).1,
        ← (D.complex.fderiv_coordinates n φ.val hφ).1,apply_sourceHamiltonianDirection]
      change sourceBracket h2p _ _ φ.val = _
      rw [(D.complex.sourceBracket_canonical h2p n m φ).2.1]
      simp [lp.single_apply,Pi.single_apply]
    · rw [(D.complex.jacobian_coordinates φ.val hφ _ n).2,
        ← (D.complex.fderiv_coordinates n φ.val hφ).2,apply_sourceHamiltonianDirection]
      simpa [sourceBracket] using (D.complex.sourceBracket_canonical h2p n m φ).2.2

/-- The normalized images swap the gradient labels: AKbˣ=-dʸ and AKbʸ=-dˣ. -/
theorem normalizedJacobian_hamiltonian_coordinates (D : SourceSection16OriginalData hp hp1 W₀ W V s)
    (h2p : 2 ≤ p) (φ : realTypeSourceSubmodule p) (m : ℤ) :
    sourceBirkhoffNormalizedJacobian hp hp1 s φ.val
      (sourceHamiltonianDirection h2p (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 m) φ.val)) =
        -sourceBirkhoffFreeYGradient p (-m) ∧
    sourceBirkhoffNormalizedJacobian hp hp1 s φ.val
      (sourceHamiltonianDirection h2p (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 m) φ.val)) =
        -sourceBirkhoffFreeXGradient p (-m) := by
  have h := D.jacobian_hamiltonian_coordinates h2p φ m
  change sourceBirkhoffFourierInverse (sourceBirkhoffJacobian hp hp1 s φ.val _) = _ ∧
    sourceBirkhoffFourierInverse (sourceBirkhoffJacobian hp hp1 s φ.val _) = _
  rw [h.1,h.2,map_neg]
  constructor
  · simpa only [neg_neg] using (sourceBirkhoffFourierInverse_y_mode (p := p) (-m))
  · congr 1
    simpa using (sourceBirkhoffFourierInverse_single (p := p) (-m) 1 0)

/-- At every real source the unswapped x-gradient formula printed on p. 78 is false. -/
theorem normalizedJacobian_hamiltonian_x_ne_printed (D : SourceSection16OriginalData hp hp1 W₀ W V s)
    (h2p : 2 ≤ p) (φ : realTypeSourceSubmodule p) (m : ℤ) :
    sourceBirkhoffNormalizedJacobian hp hp1 s φ.val
      (sourceHamiltonianDirection h2p (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 m) φ.val)) ≠
        -sourceBirkhoffFreeXGradient p (-m) := by
  rw [(D.normalizedJacobian_hamiltonian_coordinates h2p φ m).1]
  have hi : sourceBirkhoffFourierInverse (lp.single p m 1,0) =
      sourceBirkhoffFreeXGradient p (-m) := by
    simpa using (sourceBirkhoffFourierInverse_single (p := p) (-m) 1 0)
  have hx : sourceBirkhoffFourier (sourceBirkhoffFreeXGradient p (-m)) = (lp.single p m 1,0) := by
    rw [← hi,sourceBirkhoffFourier_fourierInverse]
  intro he
  have h := congrArg (fun v : CoeffPair p => (sourceBirkhoffFourier v).1 m) he
  rw [map_neg,map_neg,sourceBirkhoffFourier_freeY,hx] at h
  norm_num at h

end NLS.ZakharovShabat.SourceSection16OriginalData
