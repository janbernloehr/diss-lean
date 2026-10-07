import NLS.Dynamics.FiniteHamiltonianPhaseDerivative
import NLS.ZakharovShabat.SourceOrdinaryFlowAnalytic
import NLS.ZakharovShabat.SourceBirkhoffFiniteSupport
import NLS.ZakharovShabat.SourceComplexActionHamiltonian

/-! # Ordinary spectral flow with the physical Hamiltonian time orientation

The original ordinarySourceFlow retains equation (4.14)'s printed signs.
Its time reversal uses the signs proved from the source action Hamiltonians.
Finite-gap trajectories have an actual derivative in the full source norm,
computed by the inverse Birkhoff Jacobian. Physical PDE identification and
the continuous extension of the classical solution map are proved in
subsequent finite-gap and compact-time modules.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Finite-gap sources have finite support in both actual complex Birkhoff components. -/
theorem SourceBirkhoffMapComplexData.exists_complex_support_finiteGap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ S : Finset ℤ, ∀ n ∉ S,
      (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n = 0 ∧
        (sourceComplexBirkhoffMap hp hp1 t φ.val).2 n = 0 := by
  classical
  refine ⟨hf.toFinset,fun n hn => ?_⟩
  have hg : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0 := by
    rw [sourcePeriodicGapDisplacement_apply]
    by_contra h
    exact hn (hf.mem_toFinset.mpr h)
  have hz := D.real_closed_gap_zero φ.val (D.real_subset φ.property) φ.property n hg
  simp only [sourceComplexBirkhoffMap,Birkhoff.rectangularToComplex_fst,
    Birkhoff.rectangularToComplex_snd,hz.1,hz.2,mul_zero,sub_zero,add_zero,and_self]

namespace SourceAbelianMomentAtlas

/-- The ordinary flow oriented by the original source Poisson bracket. -/
def hamiltonianOrdinarySourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) : realTypeSourceSubmodule p :=
  A.ordinarySourceFlow D hp2 φ (-τ)

/-- The actual complex coordinates have the Hamiltonian phase orientation. -/
theorem complex_map_hamiltonianOrdinarySourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    sourceComplexBirkhoffMap hp hp1 t (A.hamiltonianOrdinarySourceFlow D hp2 φ τ).val =
      Birkhoff.hamiltonianPhaseFlow (A.ordinaryPhaseFrequency hp2 φ) τ
        (sourceComplexBirkhoffMap hp hp1 t φ.val) :=
  A.complex_map_ordinarySourceFlow D hp2 φ (-τ)

@[simp] theorem hamiltonianOrdinarySourceFlow_zero (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) : A.hamiltonianOrdinarySourceFlow D hp2 φ 0 = φ := by
  simp [hamiltonianOrdinarySourceFlow]

/-- Reversing time preserves the global group law. -/
theorem hamiltonianOrdinarySourceFlow_add (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ σ : ℝ) :
    A.hamiltonianOrdinarySourceFlow D hp2 (A.hamiltonianOrdinarySourceFlow D hp2 φ σ) τ =
      A.hamiltonianOrdinarySourceFlow D hp2 φ (τ+σ) := by
  simp only [hamiltonianOrdinarySourceFlow,A.ordinarySourceFlow_add hs,neg_add]

/-- Initial-data analyticity is unchanged by the explicit time reversal. -/
theorem analytic_hamiltonianOrdinarySourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (τ : ℝ) :
    AnalyticOnNhd ℝ (fun φ => A.hamiltonianOrdinarySourceFlow D hp2 φ τ) univ :=
  A.analytic_ordinarySourceFlow hs hP hr D hp2 (-τ)

/-- Joint continuity survives the Hamiltonian time orientation. -/
theorem continuous_hamiltonianOrdinarySourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) :
    Continuous (fun x : ℝ × realTypeSourceSubmodule p =>
      A.hamiltonianOrdinarySourceFlow D hp2 x.2 x.1) := by
  have hg : Continuous (fun x : ℝ × realTypeSourceSubmodule p => (-x.1,x.2)) :=
    continuous_fst.neg.prodMk continuous_snd
  simpa only [Function.comp_def,hamiltonianOrdinarySourceFlow] using!
    (A.continuous_ordinarySourceFlow hs hP hr D hp2).comp hg

/-- Every original spectral action is conserved with the physical time orientation. -/
theorem hamiltonianOrdinarySourceFlow_action (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    sourceComplexAction hp hp1 n (A.hamiltonianOrdinarySourceFlow D hp2 φ τ).val =
      sourceComplexAction hp hp1 n φ.val :=
  A.ordinarySourceFlow_action D hp2 φ (-τ) n

/-- The same physical mass is conserved by the Hamiltonian-oriented group. -/
theorem hamiltonianOrdinarySourceFlow_mass (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    sourceOrdinaryMass hp2 (A.hamiltonianOrdinarySourceFlow D hp2 φ τ) = sourceOrdinaryMass hp2 φ :=
  A.ordinarySourceFlow_mass D hp2 φ (-τ)

/-- An explicit full-norm source derivative for every finite complex-coordinate support. -/
theorem hasDerivAt_hamiltonianOrdinarySourceFlow_of_support
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hz : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 t φ.val).2 n = 0) (τ : ℝ) :
    HasDerivAt (fun σ => A.hamiltonianOrdinarySourceFlow D hp2 φ σ)
      ((D.realJacobianEquivAll (A.hamiltonianOrdinarySourceFlow D hp2 φ τ)).symm
        (Birkhoff.decodeReal (Birkhoff.finiteHamiltonianPhaseVelocity
          (A.ordinaryPhaseFrequency hp2 φ) S
          (Birkhoff.hamiltonianPhaseFlow (A.ordinaryPhaseFrequency hp2 φ) τ
            (sourceComplexBirkhoffMap hp hp1 t φ.val))))) τ := by
  have hd := Birkhoff.hasDerivAt_hamiltonianPhaseFlow_of_support
    (A.ordinaryPhaseFrequency hp2 φ) S (sourceComplexBirkhoffMap hp hp1 t φ.val) hz τ
  have hr := (Birkhoff.decodeReal (p := p)).hasFDerivAt.comp_hasDerivAt τ hd
  exact (D.realHomeomorph_symm_hasStrictFDerivAt hp2 _).hasFDerivAt.comp_hasDerivAt τ hr

/-- Every actual finite-gap source has a differentiable Hamiltonian-oriented spectral trajectory. -/
theorem differentiable_hamiltonianOrdinarySourceFlow_finiteGap
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    Differentiable ℝ (fun τ => A.hamiltonianOrdinarySourceFlow D hp2 φ τ) := by
  obtain ⟨S,hS⟩ := D.exists_complex_support_finiteGap φ hf
  intro τ
  exact (A.hasDerivAt_hamiltonianOrdinarySourceFlow_of_support D hp2 φ S hS τ).differentiableAt

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
