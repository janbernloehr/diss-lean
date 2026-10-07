import NLS.Dynamics.FiniteHamiltonianPhaseDerivative
import NLS.ZakharovShabat.SourceRenormalizedFlowAnalytic
import NLS.ZakharovShabat.SourceHamiltonianOrdinaryFlow
import NLS.ZakharovShabat.SourceBirkhoffFiniteSupport
import NLS.ZakharovShabat.SourceComplexActionHamiltonian

/-! # Renormalized spectral flow with the physical Hamiltonian orientation

Time reversal gives the signs of the original source action Hamiltonians.
The flow preserves actions and physical mass, is analytic in initial data,
and is differentiable in the full source norm on finite-gap trajectories.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

namespace SourceAbelianMomentAtlas

/-- The renormalized flow oriented by the original source Poisson bracket. -/
def hamiltonianRenormalizedSourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) : realTypeSourceSubmodule p :=
  A.renormalizedSourceFlow D hp2 φ (-τ)

/-- The actual complex coordinates have the Hamiltonian phase orientation. -/
theorem complex_map_hamiltonianRenormalizedSourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    sourceComplexBirkhoffMap hp hp1 t (A.hamiltonianRenormalizedSourceFlow D hp2 φ τ).val =
      Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) τ
        (sourceComplexBirkhoffMap hp hp1 t φ.val) :=
  A.complex_map_renormalizedSourceFlow D hp2 φ (-τ)

@[simp] theorem hamiltonianRenormalizedSourceFlow_zero (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) : A.hamiltonianRenormalizedSourceFlow D hp2 φ 0 = φ := by
  simp [hamiltonianRenormalizedSourceFlow]

/-- Reversing time preserves the global group law. -/
theorem hamiltonianRenormalizedSourceFlow_add (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ σ : ℝ) :
    A.hamiltonianRenormalizedSourceFlow D hp2 (A.hamiltonianRenormalizedSourceFlow D hp2 φ σ) τ =
      A.hamiltonianRenormalizedSourceFlow D hp2 φ (τ+σ) := by
  simp only [hamiltonianRenormalizedSourceFlow,A.renormalizedSourceFlow_add hs,neg_add]

/-- Initial-data analyticity is unchanged by the explicit time reversal. -/
theorem analytic_hamiltonianRenormalizedSourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (τ : ℝ) :
    AnalyticOnNhd ℝ (fun φ => A.hamiltonianRenormalizedSourceFlow D hp2 φ τ) univ :=
  A.analytic_renormalizedSourceFlow hs hP hr D hp2 (-τ)

/-- Joint continuity survives the Hamiltonian time orientation. -/
theorem continuous_hamiltonianRenormalizedSourceFlow (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) :
    Continuous (fun x : ℝ × realTypeSourceSubmodule p =>
      A.hamiltonianRenormalizedSourceFlow D hp2 x.2 x.1) := by
  have hg : Continuous (fun x : ℝ × realTypeSourceSubmodule p => (-x.1,x.2)) :=
    continuous_fst.neg.prodMk continuous_snd
  simpa only [Function.comp_def,hamiltonianRenormalizedSourceFlow] using!
    (A.continuous_renormalizedSourceFlow hs hP hr D hp2).comp hg

/-- Every original spectral action is conserved with the physical time orientation. -/
theorem hamiltonianRenormalizedSourceFlow_action (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    sourceComplexAction hp hp1 n (A.hamiltonianRenormalizedSourceFlow D hp2 φ τ).val =
      sourceComplexAction hp hp1 n φ.val :=
  A.renormalizedSourceFlow_action D hp2 φ (-τ) n

/-- The same physical mass is conserved by the Hamiltonian-oriented group. -/
theorem hamiltonianRenormalizedSourceFlow_mass (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    sourceOrdinaryMass hp2 (A.hamiltonianRenormalizedSourceFlow D hp2 φ τ) = sourceOrdinaryMass hp2 φ :=
  sourceOrdinaryMass_eq_of_actions hp hp1 hp2 _ φ (A.hamiltonianRenormalizedSourceFlow_action D hp2 φ τ)

/-- An explicit full-norm source derivative for every finite complex-coordinate support. -/
theorem hasDerivAt_hamiltonianRenormalizedSourceFlow_of_support
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hz : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 t φ.val).2 n = 0) (τ : ℝ) :
    HasDerivAt (fun σ => A.hamiltonianRenormalizedSourceFlow D hp2 φ σ)
      ((D.realJacobianEquivAll (A.hamiltonianRenormalizedSourceFlow D hp2 φ τ)).symm
        (Birkhoff.decodeReal (Birkhoff.finiteHamiltonianPhaseVelocity
          (A.phaseFrequency φ) S
          (Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) τ
            (sourceComplexBirkhoffMap hp hp1 t φ.val))))) τ := by
  have hd := Birkhoff.hasDerivAt_hamiltonianPhaseFlow_of_support
    (A.phaseFrequency φ) S (sourceComplexBirkhoffMap hp hp1 t φ.val) hz τ
  have hr := (Birkhoff.decodeReal (p := p)).hasFDerivAt.comp_hasDerivAt τ hd
  exact (D.realHomeomorph_symm_hasStrictFDerivAt hp2 _).hasFDerivAt.comp_hasDerivAt τ hr

/-- Every actual finite-gap source has a differentiable Hamiltonian-oriented spectral trajectory. -/
theorem differentiable_hamiltonianRenormalizedSourceFlow_finiteGap
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    Differentiable ℝ (fun τ => A.hamiltonianRenormalizedSourceFlow D hp2 φ τ) := by
  obtain ⟨S,hS⟩ := D.exists_complex_support_finiteGap φ hf
  intro τ
  exact (A.hasDerivAt_hamiltonianRenormalizedSourceFlow_of_support D hp2 φ S hS τ).differentiableAt

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
