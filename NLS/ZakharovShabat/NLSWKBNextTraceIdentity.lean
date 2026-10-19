import NLS.ZakharovShabat.NLSWKBTraceErrorDecomposition
import NLS.ZakharovShabat.NLSHamiltonianPhaseIncrement

/-! # The exact next-phase trace identity

The determinant-weighted trace error is expressed by the corrected diagonals, off-diagonals, leading terms, and a scalar correction.
-/

noncomputable section
open Set Complex
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The scalar error in the next Hamiltonian trace after its diagonal
phase primitives have been included. -/
def nlsHamiltonianTraceIncrementError (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  2*cos (I*nlsHamiltonianPhase a b (N+1) z)-2*cos (I*nlsHamiltonianPhase a b N z)+
    nlsWKBDiagonalPhasePrimitive a b N z 1+nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1

/-- The residual scalar correction in the determinant-weighted trace. -/
def nlsWKBNextTraceCorrectionError (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  -(1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z)*
    nlsHamiltonianTraceIncrementError a b N z-
    nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z*
      (nlsWKBDiagonalPhasePrimitive a b N z 1+nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1)

/-- The actual trace at the next Hamiltonian phase is expressed using
the two corrected diagonal remainders and the small initial factors. -/
theorem classicalDiscriminant_sub_next_wkb_phase_exact
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ)
    (hd : 1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z ≠ 0) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let E := nlsWKBFirstRemainder a b ha.continuous hb.continuous N z 1
    let F := nlsWKBSecondRemainder a b ha.continuous hb.continuous N z 1
    (1-p*q)*(classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z-
      2*cos (I*nlsHamiltonianPhase a b (N+1) z)) =
      p*nlsWKBLeadingTerm (-b) (-a) N (-z) 1+q*nlsWKBLeadingTerm a b N z 1+
      p*F.1+q*E.2-(E.1-nlsWKBDiagonalPhasePrimitive a b N z 1)-
      (F.2-nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1)+
      nlsWKBNextTraceCorrectionError a b N z := by
  have h := classicalDiscriminant_sub_wkb_phase_exact a b ha hb hpa hpb N z hd
  dsimp only at h ⊢
  dsimp only [nlsWKBNextTraceCorrectionError,nlsHamiltonianTraceIncrementError]
  linear_combination h

end NLS.ZakharovShabat
