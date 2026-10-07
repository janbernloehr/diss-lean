import NLS.ZakharovShabat.SourceOrdinaryFlowAnalytic
import NLS.ZakharovShabat.SourceOrdinaryMassShift

/-! # Constructed global ordinary NLS spectral dynamics

The actual moment atlas and Birkhoff family give a global continuous group
with analytic complete trajectories and analytic inverse time maps for
1 < p ≤ 2. The mass correction is the original physical mass and total
action. Agreement with classical PDE solutions remains a separate step.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Global ordinary spectral dynamics with analytic compact-time source dependence,
action and physical-mass conservation, and bi-analytic time maps. -/
theorem exists_analytic_ordinarySourceTrajectories (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W P : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ hs : SourcePsiSquaredGapComplexExtension hp hp1 P s,
    ∃ hP : IsOpen P, ∃ hr : realTypeSourceLocus p ⊆ P,
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
      (∀ T : ℝ, AnalyticOnNhd ℝ (A.ordinarySourceTrajectoryOn hs hP hr D hp2 T) univ) ∧
      Continuous (fun x : ℝ × realTypeSourceSubmodule p => A.ordinarySourceFlow D hp2 x.2 x.1) ∧
      (∀ φ, A.ordinarySourceFlow D hp2 φ 0 = φ) ∧
      (∀ φ τ σ, A.ordinarySourceFlow D hp2 (A.ordinarySourceFlow D hp2 φ σ) τ =
        A.ordinarySourceFlow D hp2 φ (τ+σ)) ∧
      (∀ φ τ n, sourceComplexAction hp hp1 n (A.ordinarySourceFlow D hp2 φ τ).val =
        sourceComplexAction hp hp1 n φ.val) ∧
      (∀ φ τ, sourceOrdinaryMass hp2 (A.ordinarySourceFlow D hp2 φ τ) = sourceOrdinaryMass hp2 φ) ∧
      ∀ τ : ℝ, ∃ e : realTypeSourceSubmodule p ≃ₜ realTypeSourceSubmodule p,
        (∀ φ, e φ = A.ordinarySourceFlow D hp2 φ τ) ∧
        (∀ φ, e.symm φ = A.ordinarySourceFlow D hp2 φ (-τ)) ∧
        AnalyticOnNhd ℝ e univ ∧ AnalyticOnNhd ℝ e.symm univ := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨W₀,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  refine ⟨W,P,s,A,hs,hP,hr,W₀,B,X,t,D,
    A.analytic_ordinarySourceTrajectoryOn hs hP hr D hp2,
    A.continuous_ordinarySourceFlow hs hP hr D hp2,
    A.ordinarySourceFlow_zero D hp2,
    A.ordinarySourceFlow_add hs.toSourcePsiIsolatingComplexExtension D hp2,
    A.ordinarySourceFlow_action D hp2,A.ordinarySourceFlow_mass D hp2,?_⟩
  intro τ
  exact ⟨A.ordinarySourceHomeomorph hs hP hr D hp2 τ,fun _ => rfl,fun _ => rfl,
    A.ordinarySourceHomeomorph_analytic hs hP hr D hp2 τ⟩

end NLS.ZakharovShabat
