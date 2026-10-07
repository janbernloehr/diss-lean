import NLS.ZakharovShabat.SourceHamiltonianFlowExponent
import NLS.ZakharovShabat.SourceHamiltonianTrajectories
import NLS.ZakharovShabat.ClassicalNLSNonextension

/-! # The continuous extension of the actual classical NLS solution map

For `1 < p ≤ 2`, the Hamiltonian-oriented source flow agrees with the actual
classical finite-gap trajectories. Density then identifies it as the unique
continuous extension in the uniform compact-time source norm. This is a
solution-map extension statement, not a claim of weak-PDE uniqueness for
arbitrary rough trajectories.
-/
noncomputable section
open Set Filter Topology NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous extension on `[-T,T]` of the actual finite-gap classical NLS
solution map, expressed through its physical scalar Fourier integrals. -/
def IsContinuousClassicalNLSExtension (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ)
    (F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p)) : Prop :=
  Continuous F ∧ ∀ φ : realTypeSourceSubmodule p, ∀ hf : φ ∈ sourceFiniteGapLocus hp hp1,
    ∀ time : Icc (-T) T, ∀ n : ℤ, (F φ time).val.fst n =
      periodOneCoefficient (fun x : ℝ => sourceFiniteGapClassicalTrajectory hp hp1 φ hf time.val
        (x : AddCircle (2 : ℝ))) n

/-- Density of actual finite-gap sources makes a continuous extension unique. -/
theorem IsContinuousClassicalNLSExtension.unique
    {hp : p ≠ ⊤} {hp1 : 1 < p} {T : ℝ}
    {F G : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p)}
    (hF : IsContinuousClassicalNLSExtension hp hp1 T F)
    (hG : IsContinuousClassicalNLSExtension hp hp1 T G) : F = G := by
  funext φ
  obtain ⟨ψ,hf,hψ⟩ := exists_sourceFiniteGap_sequence hp hp1 φ
  have he : (fun j => F (ψ j)) = fun j => G (ψ j) := by
    funext j
    apply ContinuousMap.ext
    intro time
    apply realTypeSource_eq_of_fst
    intro n
    exact (hF.2 (ψ j) (hf j) time n).trans (hG.2 (ψ j) (hf j) time n).symm
  have hlim := hF.1.continuousAt.tendsto.comp hψ
  change Tendsto (fun j => F (ψ j)) atTop (𝓝 (F φ)) at hlim
  rw [he] at hlim
  exact tendsto_nhds_unique hlim (hG.1.continuousAt.tendsto.comp hψ)

/-- Every real source is a compact-time uniform limit of actual finite-gap
classical solutions, with initial convergence in the original source norm. -/
theorem IsContinuousClassicalNLSExtension.exists_classical_approximation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {T : ℝ}
    {F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p)}
    (hF : IsContinuousClassicalNLSExtension hp hp1 T F) (φ : realTypeSourceSubmodule p) :
    ∃ ψ : ℕ → realTypeSourceSubmodule p, ∃ hf : ∀ j, ψ j ∈ sourceFiniteGapLocus hp hp1,
      Tendsto ψ atTop (𝓝 φ) ∧ Tendsto (fun j => F (ψ j)) atTop (𝓝 (F φ)) ∧
      ∀ j (time : Icc (-T) T) (n : ℤ), (F (ψ j) time).val.fst n =
        periodOneCoefficient (fun x : ℝ => sourceFiniteGapClassicalTrajectory hp hp1 (ψ j) (hf j) time.val
          (x : AddCircle (2 : ℝ))) n := by
  obtain ⟨ψ,hf,hψ⟩ := exists_sourceFiniteGap_sequence hp hp1 φ
  exact ⟨ψ,hf,hψ,hF.1.continuousAt.tendsto.comp hψ,fun j => hF.2 (ψ j) (hf j)⟩

/-- Every convergent finite-gap approximation, with any supplied classical
coefficient trajectories, has the same compact-time limit. No continuity
of the approximation family as a function of initial data is assumed. -/
theorem IsContinuousClassicalNLSExtension.tendsto_classical_approximation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {T : ℝ}
    {F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p)}
    (hF : IsContinuousClassicalNLSExtension hp hp1 T F) {ι : Type*} {l : Filter ι}
    (φ : realTypeSourceSubmodule p) (ψ : ι → realTypeSourceSubmodule p)
    (hf : ∀ j, ψ j ∈ sourceFiniteGapLocus hp hp1) (hψ : Tendsto ψ l (𝓝 φ))
    (G : ι → C(Icc (-T) T,realTypeSourceSubmodule p))
    (hG : ∀ j (time : Icc (-T) T) (n : ℤ), (G j time).val.fst n =
      periodOneCoefficient (fun x : ℝ => sourceFiniteGapClassicalTrajectory hp hp1 (ψ j) (hf j) time.val
        (x : AddCircle (2 : ℝ))) n) : Tendsto G l (𝓝 (F φ)) := by
  have he : G = fun j => F (ψ j) := by
    funext j
    apply ContinuousMap.ext
    intro time
    apply realTypeSource_eq_of_fst
    intro n
    exact (hG j time n).trans (hF.2 (ψ j) (hf j) time n).symm
  rw [he]
  exact hF.1.continuousAt.tendsto.comp hψ

namespace SourceAbelianMomentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {V B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The physical source flow at every exponent at most two has exactly the
Fourier coefficients of the unique classical finite-gap solution. -/
theorem hamiltonianOrdinarySourceFlow_fst_eq_classical
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (time : ℝ) (n : ℤ) :
    (A.hamiltonianOrdinarySourceFlow D hp2 φ time).val.fst n =
      periodOneCoefficient (fun x : ℝ => sourceFiniteGapClassicalTrajectory hp hp1 φ hf time
        (x : AddCircle (2 : ℝ))) n := by
  obtain ⟨W₂,P₂,_,_,_,_,s₂,hs₂,⟨H⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V₂,B₂,X₂,t₂,E⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  have hi := A.hamiltonianOrdinarySourceFlow_exponent H hs hs₂.toSourcePsiIsolatingComplexExtension
    D E hp2 le_rfl φ time
  have hi' := congrArg (fun ξ : realTypeSourceSubmodule 2 => ξ.val.fst n) hi
  have hm := sourceFiniteGapHilbertModel_eq_of_coefficients hp hp1 φ hf
    (realTypeSourceExponentInclusion hp2 φ) (fun _ => ⟨rfl,rfl⟩)
  have hc := H.periodOneCoefficient_classicalNLS_eq_hamiltonianFlow
    hs₂.toSourcePsiIsolatingComplexExtension E hp hp1 φ hf
    (sourceFiniteGapClassicalTrajectory hp hp1 φ hf)
    (sourceFiniteGapClassicalTrajectory_spec hp hp1 φ hf).1
    (sourceFiniteGapClassicalTrajectory_spec hp hp1 φ hf).2 time n
  rw [hm] at hc
  exact hi'.trans hc.symm

/-- The analytic Hamiltonian-oriented trajectory map extends the actual
classical finite-gap solution map in the original source exponent. -/
theorem isContinuousClassicalNLSExtension_hamiltonianTrajectory
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) (T : ℝ) :
    IsContinuousClassicalNLSExtension hp hp1 T (A.hamiltonianOrdinarySourceTrajectoryOn hs hP hr D hp2 T) :=
  ⟨A.continuous_hamiltonianOrdinarySourceTrajectoryOn hs hP hr D hp2 T,
    fun φ hf time n => A.hamiltonianOrdinarySourceFlow_fst_eq_classical hs.toSourcePsiIsolatingComplexExtension
      D hp2 φ hf time.val n⟩

end SourceAbelianMomentAtlas

/-- Any continuous extension of the classical solution map is automatically
real analytic when `1 < p ≤ 2`, because it equals the constructed analytic map. -/
theorem IsContinuousClassicalNLSExtension.analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {T : ℝ}
    {F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p)}
    (hF : IsContinuousClassicalNLSExtension hp hp1 T F) (hp2 : p ≤ 2) : AnalyticOnNhd ℝ F univ := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  rw [hF.unique (A.isContinuousClassicalNLSExtension_hamiltonianTrajectory hs hP hr D hp2 T)]
  exact A.analytic_hamiltonianOrdinarySourceTrajectoryOn hs hP hr D hp2 T

/-- The continuous extension of the physical finite-gap classical NLS map
exists uniquely for `1 < p ≤ 2`, on every compact time interval. -/
theorem existsUnique_continuous_classicalNLSExtension
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (T : ℝ) :
    ∃! F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p),
      IsContinuousClassicalNLSExtension hp hp1 T F := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  have he := A.isContinuousClassicalNLSExtension_hamiltonianTrajectory hs hP hr D hp2 T
  exact ⟨A.hamiltonianOrdinarySourceTrajectoryOn hs hP hr D hp2 T,he,fun _ hF => hF.unique he⟩

/-- One global physical NLS extension group has analytic compact-time source
maps. All spectral data are constructed; its reference values are actual
classical solutions, and each compact-time extension is unique by density. -/
theorem exists_global_analytic_classicalNLSExtension
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ S : realTypeSourceSubmodule p → ℝ → realTypeSourceSubmodule p,
      Continuous (fun x : ℝ × realTypeSourceSubmodule p => S x.2 x.1) ∧
      (∀ φ, S φ 0 = φ) ∧
      (∀ φ (time r : ℝ), S (S φ r) time = S φ (time+r)) ∧
      ∀ T : ℝ, ∃ F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p),
        AnalyticOnNhd ℝ F univ ∧ IsContinuousClassicalNLSExtension hp hp1 T F ∧
        ∀ φ (time : Icc (-T) T), F φ time = S φ time.val := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  refine ⟨A.hamiltonianOrdinarySourceFlow D hp2,
    A.continuous_hamiltonianOrdinarySourceFlow hs hP hr D hp2,
    A.hamiltonianOrdinarySourceFlow_zero D hp2,
    A.hamiltonianOrdinarySourceFlow_add hs.toSourcePsiIsolatingComplexExtension D hp2,?_⟩
  intro T
  exact ⟨A.hamiltonianOrdinarySourceTrajectoryOn hs hP hr D hp2 T,
    A.analytic_hamiltonianOrdinarySourceTrajectoryOn hs hP hr D hp2 T,
    A.isContinuousClassicalNLSExtension_hamiltonianTrajectory hs hP hr D hp2 T,fun _ _ => rfl⟩

end NLS.ZakharovShabat
