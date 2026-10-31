import NLS.Dynamics.PhaseContinuityEstimate
import NLS.ZakharovShabat.SourceSection22Phases

/-! # Section 22 head and tail estimates for the original physical flow

The actual moment frequencies and original Birkhoff family retain the
finite-p pair norm and exact 2^p tail factor. Coordinate-parameterized
trajectories keep the original image guard, including above exponent two.
-/
noncomputable section
namespace NLS.ZakharovShabat.SourceSection20Data
open Set
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The full head/tail estimate for the original physical trajectory, with the
original moment frequency and the component-sum norm on complex coordinates. -/
theorem hamiltonian_phase_increment_rpow_le (T : ℝ) (φ : realTypeSourceSubmodule p)
    (t u : Icc (-T) T) (S : Finset ℤ) :
    ‖(CoeffPair.toMax p).symm
      (A.hamiltonianComplexPhaseTrajectoryOn T φ.val t-A.hamiltonianComplexPhaseTrajectoryOn T φ.val u)‖ ^ p.toReal ≤
      (∑ n ∈ S, ‖Complex.exp ((((t.val-u.val)*A.phaseFrequency φ n : ℝ) : ℂ)*Complex.I)-1‖ ^ p.toReal *
        (‖(sourceComplexBirkhoffMap hp hp1 s φ.val).1 n‖ ^ p.toReal+
          ‖(sourceComplexBirkhoffMap hp hp1 s φ.val).2 n‖ ^ p.toReal)) +
      (2 : ℝ) ^ p.toReal * ∑' n : {n : ℤ // n ∉ S},
        (‖(sourceComplexBirkhoffMap hp hp1 s φ.val).1 n.val‖ ^ p.toReal+
          ‖(sourceComplexBirkhoffMap hp hp1 s φ.val).2 n.val‖ ^ p.toReal) := by
  rw [Q.hamiltonian_phase_real T φ t,Q.hamiltonian_phase_real T φ u]
  exact Birkhoff.norm_hamiltonianPhaseFlow_sub_rpow_le hp _ _ _ _ S

/-- The same estimate on the actual original coordinate image. The inverse
keeps its image guard at every finite source exponent above one. -/
theorem hamiltonian_coordinate_increment_rpow_le (T : ℝ) (z : RealCoeff p × RealCoeff p)
    (hz : z ∈ range (sourceRealBirkhoffMap hp hp1 s)) (t u : Icc (-T) T) (S : Finset ℤ) :
    ‖(CoeffPair.toMax p).symm
      (A.hamiltonianCoordinateTrajectoryOn D.complex T z t-A.hamiltonianCoordinateTrajectoryOn D.complex T z u)‖ ^ p.toReal ≤
      (∑ n ∈ S, ‖Complex.exp ((((t.val-u.val)*A.phaseFrequency (D.complex.realImageInverse z) n : ℝ) : ℂ)*Complex.I)-1‖ ^ p.toReal *
        (‖(Birkhoff.encodeReal z).1 n‖ ^ p.toReal+‖(Birkhoff.encodeReal z).2 n‖ ^ p.toReal)) +
      (2 : ℝ) ^ p.toReal * ∑' n : {n : ℤ // n ∉ S},
        (‖(Birkhoff.encodeReal z).1 n.val‖ ^ p.toReal+‖(Birkhoff.encodeReal z).2 n.val‖ ^ p.toReal) := by
  rw [Q.hamiltonian_coordinate_apply T z hz t,Q.hamiltonian_coordinate_apply T z hz u]
  exact Birkhoff.norm_hamiltonianPhaseFlow_sub_rpow_le hp _ _ _ _ S

end NLS.ZakharovShabat.SourceSection20Data
