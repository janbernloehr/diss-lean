import NLS.ZakharovShabat.SourceSection20Original
import NLS.ZakharovShabat.SourceRenormalizedPhaseAnalytic
import NLS.ZakharovShabat.SourceBirkhoffImageInverse
import NLS.ZakharovShabat.SourceHamiltonianTrajectories

/-! # Section 22 trajectories on the original source and coordinate domains

Both the printed phases and their physical time reversal are analytic in
the full compact-time norm on the existing Section 20 neighborhood. The
physical trajectories retain the original map, moments, and frequencies.
Their dependence on initial coordinates is analytic on the actual open
Birkhoff image, at every finite exponent above one.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}

namespace SourceAbelianMomentAtlas
variable {Wa : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The complex trajectory with the time orientation of the original source Hamiltonian. -/
def hamiltonianComplexPhaseTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 Wa s)
    (T : ℝ) (ψ : CoeffPair p) : C(Icc (-T) T,Coeff p × Coeff p) :=
  (A.complexPhaseTrajectoryOn s T ψ).comp (hamiltonianTimeReflection T)

/-- The physical trajectory parameterized by the actual original rectangular coordinates.
Assertions about this total formula carry the original image condition. -/
def hamiltonianCoordinateTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 Wa s)
    {W₀ W V : Set (CoeffPair p)} (D : SourceBirkhoffMapComplexData hp hp1 W₀ W V s)
    (T : ℝ) (z : RealCoeff p × RealCoeff p) : C(Icc (-T) T,Coeff p × Coeff p) :=
  A.hamiltonianComplexPhaseTrajectoryOn T (D.realImageInverse z).val
end SourceAbelianMomentAtlas

variable {W₀ W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The retained original root family has its original open ambient domain. -/
theorem SourceSection17OriginalData.roots_open (D : SourceSection17OriginalData hp hp1 W₀ W V s) : IsOpen W := by
  obtain ⟨E,hE,_⟩ := D.previous.previous.previous.atlas
  exact hE ▸ E.toSourcePsiComplexRootAtlas.isOpen_domain

/-- All real sources remain in the retained original root domain. -/
theorem SourceSection17OriginalData.roots_real_subset (D : SourceSection17OriginalData hp hp1 W₀ W V s) : realTypeSourceLocus p ⊆ W :=
  D.complex.real_subset.trans D.complex.source_subset

namespace SourceSection20Data
variable {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The original bounded frequency correction is analytic on all of U. -/
theorem bounded_phase_correction :
    AnalyticOnNhd ℂ A.boundedPhaseCorrection U ∧
      ∀ ψ ∈ U, ∀ n, A.boundedPhaseCorrection ψ n = A.renormalizedFrequency n ψ := by
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨he,ha⟩ := Q.sequence p hp hp1 hhalf
  exact ⟨fun ψ hψ => ((Coeff.exponentInclusion (show p ≤ ⊤ from le_top)).analyticAt _).comp
    (ha ψ hψ),he⟩

/-- The literal printed phase has full compact-time complex analyticity on the original U. -/
theorem complex_phase_analytic (T : ℝ) :
    AnalyticOnNhd ℂ (A.complexPhaseTrajectoryOn s T) U := by
  intro ψ hψ
  simpa only [SourceAbelianMomentAtlas.complexPhaseTrajectoryOn,Function.comp_def] using!
    (Birkhoff.analyticAt_analyticPhaseTrajectory hp (fun n : ℤ => (2*Real.pi*n)^2)
      (⟨Subtype.val,continuous_subtype_val⟩ : C(Icc (-T) T,ℝ))
      (A.boundedPhaseCorrection ψ,sourceComplexBirkhoffMap hp hp1 s ψ)).comp
      (f := fun χ => (A.boundedPhaseCorrection χ,sourceComplexBirkhoffMap hp hp1 s χ))
      ((Q.bounded_phase_correction.1 ψ hψ).prod
        (D.complex.complex_map_analytic ψ (Q.original_subset hψ)))

/-- Time reflection retains analyticity on the same U for every compact time horizon. -/
theorem hamiltonian_phase_analytic (T : ℝ) :
    AnalyticOnNhd ℂ (A.hamiltonianComplexPhaseTrajectoryOn T) U := by
  intro ψ hψ
  exact ((ContinuousMap.compCLM ℂ (Coeff p × Coeff p) (hamiltonianTimeReflection T)).analyticAt _).comp
    (Q.complex_phase_analytic T ψ hψ)

/-- Corrected equation (4.14), with the original complex frequencies on all of U. -/
theorem hamiltonian_phase_coordinates (T : ℝ) (ψ : CoeffPair p) (hψ : ψ ∈ U)
    (τ : Icc (-T) T) (n : ℤ) :
    (A.hamiltonianComplexPhaseTrajectoryOn T ψ τ).1 n =
      Complex.exp (-(τ.val : ℂ)*Complex.I*((2*(Real.pi:ℂ)*n)^2+A.renormalizedFrequency n ψ))*
        (sourceComplexBirkhoffMap hp hp1 s ψ).1 n ∧
    (A.hamiltonianComplexPhaseTrajectoryOn T ψ τ).2 n =
      Complex.exp ((τ.val : ℂ)*Complex.I*((2*(Real.pi:ℂ)*n)^2+A.renormalizedFrequency n ψ))*
        (sourceComplexBirkhoffMap hp hp1 s ψ).2 n := by
  simp only [SourceAbelianMomentAtlas.hamiltonianComplexPhaseTrajectoryOn,ContinuousMap.comp_apply,
    SourceAbelianMomentAtlas.complexPhaseTrajectoryOn,Birkhoff.analyticPhaseTrajectory_fst,
    Birkhoff.analyticPhaseTrajectory_snd,Q.bounded_phase_correction.2 ψ hψ,
    hamiltonianTimeReflection,ContinuousMap.coe_mk]
  push_cast
  simp

/-- Real sources give the actual Hamiltonian phase flow, with no change of family. -/
theorem hamiltonian_phase_real (T : ℝ) (φ : realTypeSourceSubmodule p) (τ : Icc (-T) T) :
    A.hamiltonianComplexPhaseTrajectoryOn T φ.val τ =
      Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) τ.val
        (sourceComplexBirkhoffMap hp hp1 s φ.val) := by
  apply Prod.ext <;> ext n
  · rw [(Q.hamiltonian_phase_coordinates T φ.val (Q.real_subset φ.property) τ n).1,
      Birkhoff.hamiltonianPhaseFlow_fst]
    congr 2
    rw [Complex.ofReal_mul,Complex.ofReal_neg,A.phaseFrequency_complex Q.roots.toSourcePsiIsolatingComplexExtension]
    ring
  · rw [(Q.hamiltonian_phase_coordinates T φ.val (Q.real_subset φ.property) τ n).2,
      Birkhoff.hamiltonianPhaseFlow_snd]
    congr 2
    rw [Complex.ofReal_mul,A.phaseFrequency_complex Q.roots.toSourcePsiIsolatingComplexExtension]
    ring

/-- Full trajectory analyticity on the entire real source space. -/
theorem hamiltonian_phase_real_analytic (T : ℝ) :
    AnalyticOnNhd ℝ (fun φ : realTypeSourceSubmodule p =>
      A.hamiltonianComplexPhaseTrajectoryOn T φ.val) univ := by
  intro φ _
  exact ((Q.hamiltonian_phase_analytic T φ.val (Q.real_subset φ.property)).restrictScalars (𝕜 := ℝ)).comp
    ((realTypeSourceSubmodule p).subtypeL.analyticAt φ)

/-- Theorem 22.1(i)'s trajectory analyticity holds on the whole actual open coordinate image. -/
theorem hamiltonian_coordinate_analytic (T : ℝ) :
    AnalyticOnNhd ℝ (A.hamiltonianCoordinateTrajectoryOn D.complex T)
      (range (sourceRealBirkhoffMap hp hp1 s)) := by
  intro z hz
  exact (Q.hamiltonian_phase_real_analytic T _ (mem_univ _)).comp
    (D.complex.realImageInverse_analytic z hz)

/-- The coordinate-parameterized trajectory has exactly the intended initial pair. -/
theorem hamiltonian_coordinate_apply (T : ℝ) (z : RealCoeff p × RealCoeff p)
    (hz : z ∈ range (sourceRealBirkhoffMap hp hp1 s)) (τ : Icc (-T) T) :
    A.hamiltonianCoordinateTrajectoryOn D.complex T z τ =
      Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency (D.complex.realImageInverse z)) τ.val
        (Birkhoff.encodeReal z) := by
  rw [SourceAbelianMomentAtlas.hamiltonianCoordinateTrajectoryOn,Q.hamiltonian_phase_real,
    ← D.complex.encode_real_map,D.complex.real_map_realImageInverse z hz]

/-- The physical trajectory preserves the actual action at every complex source in U. -/
theorem hamiltonian_phase_action (T : ℝ) (ψ : CoeffPair p) (hψ : ψ ∈ U)
    (τ : Icc (-T) T) (n : ℤ) :
    (A.hamiltonianComplexPhaseTrajectoryOn T ψ τ).1 n *
      (A.hamiltonianComplexPhaseTrajectoryOn T ψ τ).2 n = sourceComplexAction hp hp1 n ψ := by
  obtain ⟨hz,hw⟩ := Q.hamiltonian_phase_coordinates T ψ hψ τ n
  rw [hz,hw]
  calc
    _ = (Complex.exp (-(τ.val : ℂ)*Complex.I*((2*(Real.pi:ℂ)*n)^2+A.renormalizedFrequency n ψ)) *
        Complex.exp ((τ.val : ℂ)*Complex.I*((2*(Real.pi:ℂ)*n)^2+A.renormalizedFrequency n ψ))) *
        ((sourceComplexBirkhoffMap hp hp1 s ψ).1 n *
          (sourceComplexBirkhoffMap hp hp1 s ψ).2 n) := by ring
    _ = (sourceComplexBirkhoffMap hp hp1 s ψ).1 n *
        (sourceComplexBirkhoffMap hp hp1 s ψ).2 n := by
      rw [← Complex.exp_add]
      have hz : -(τ.val : ℂ)*Complex.I*((2*(Real.pi:ℂ)*n)^2+A.renormalizedFrequency n ψ)+
          (τ.val : ℂ)*Complex.I*((2*(Real.pi:ℂ)*n)^2+A.renormalizedFrequency n ψ) = 0 := by ring
      rw [hz,Complex.exp_zero,one_mul]
    _ = _ := D.complex.complex_map_action ψ (Q.original_subset hψ) n

/-- The physical coordinate flow is jointly continuous in real time and initial source,
including above the globally surjective exponent range. -/
theorem hamiltonian_phase_joint_continuous :
    Continuous (fun x : ℝ × realTypeSourceSubmodule p =>
      Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency x.2) x.1
        (sourceComplexBirkhoffMap hp hp1 s x.2.val)) := by
  have hg : Continuous (fun x : ℝ × realTypeSourceSubmodule p => (-x.1,x.2)) :=
    continuous_fst.neg.prodMk continuous_snd
  simpa only [Function.comp_def,SourceAbelianMomentAtlas.renormalizedPhaseTrajectory,
    Birkhoff.hamiltonianPhaseFlow] using!
    (A.continuous_renormalizedPhaseTrajectory Q.roots D.roots_open D.roots_real_subset D.complex).comp hg

end SourceSection20Data
end NLS.ZakharovShabat
