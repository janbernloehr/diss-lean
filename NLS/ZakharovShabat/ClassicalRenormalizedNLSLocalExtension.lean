import NLS.ZakharovShabat.SourceRenormalizedImageClassicalAgreement

/-! # Local classical renormalized extensions above the Hilbert exponent

Continuity is required only on the stated initial-data neighborhood. Its
openness and actual finite-gap density give uniqueness there and uniform
compact-time convergence of every finite-gap classical approximation. The physical
image flow supplies an analytic extension around every real source.
-/
noncomputable section
open Set Filter Topology NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous classical renormalized extension on an initial-data set,
expressed through the actual physical Fourier integrals on finite-gap data. -/
def IsContinuousClassicalRenormalizedNLSExtensionOn (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ)
    (U : Set (realTypeSourceSubmodule p))
    (F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p)) : Prop :=
  ContinuousOn F U ∧ ∀ φ ∈ U, ∀ hf : φ ∈ sourceFiniteGapLocus hp hp1,
    ∀ time : Icc (-T) T, ∀ n : ℤ, (F φ time).val.fst n =
      periodOneCoefficient (fun x : ℝ => sourceFiniteGapClassicalRenormalizedTrajectory hp hp1 φ hf time.val
        (x : AddCircle (2 : ℝ))) n

/-- Actual finite-gap density makes the continuous extension unique on
any open initial-data set, independently of values outside that set. -/
theorem IsContinuousClassicalRenormalizedNLSExtensionOn.unique
    {hp : p ≠ ⊤} {hp1 : 1 < p} {T : ℝ} {U : Set (realTypeSourceSubmodule p)}
    {F G : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p)}
    (hF : IsContinuousClassicalRenormalizedNLSExtensionOn hp hp1 T U F)
    (hG : IsContinuousClassicalRenormalizedNLSExtensionOn hp hp1 T U G) (hU : IsOpen U) : EqOn F G U := by
  intro φ hφ
  obtain ⟨ψ,hf,hψ⟩ := exists_sourceFiniteGap_sequence hp hp1 φ
  have hm := hψ.eventually (hU.mem_nhds hφ)
  have he : (fun j => F (ψ j)) =ᶠ[atTop] fun j => G (ψ j) := by
    filter_upwards [hm] with j hj
    apply ContinuousMap.ext
    intro time
    apply realTypeSource_eq_of_fst
    intro n
    exact (hF.2 (ψ j) hj (hf j) time n).trans (hG.2 (ψ j) hj (hf j) time n).symm
  have hlim := ((hF.1 φ hφ).continuousAt (hU.mem_nhds hφ)).tendsto.comp hψ
  exact tendsto_nhds_unique (hlim.congr' he) (((hG.1 φ hφ).continuousAt (hU.mem_nhds hφ)).tendsto.comp hψ)

/-- Every classical finite-gap approximation converges in the uniform path
norm near an interior initial source; early approximants may lie outside U. -/
theorem IsContinuousClassicalRenormalizedNLSExtensionOn.tendsto_classical_approximation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {T : ℝ} {U : Set (realTypeSourceSubmodule p)}
    {F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p)}
    (hF : IsContinuousClassicalRenormalizedNLSExtensionOn hp hp1 T U F) (hU : IsOpen U)
    {ι : Type*} {l : Filter ι} (φ : realTypeSourceSubmodule p) (hφ : φ ∈ U)
    (ψ : ι → realTypeSourceSubmodule p) (hf : ∀ j, ψ j ∈ sourceFiniteGapLocus hp hp1)
    (hψ : Tendsto ψ l (𝓝 φ)) (G : ι → C(Icc (-T) T,realTypeSourceSubmodule p))
    (hG : ∀ j (time : Icc (-T) T) (n : ℤ), (G j time).val.fst n =
      periodOneCoefficient (fun x : ℝ => sourceFiniteGapClassicalRenormalizedTrajectory hp hp1 (ψ j) (hf j)
        time.val (x : AddCircle (2 : ℝ))) n) : Tendsto G l (𝓝 (F φ)) := by
  have he : (fun j => F (ψ j)) =ᶠ[l] G := by
    filter_upwards [hψ.eventually (hU.mem_nhds hφ)] with j hj
    apply ContinuousMap.ext
    intro time
    apply realTypeSource_eq_of_fst
    intro n
    exact (hF.2 (ψ j) hj (hf j) time n).trans (hG j time n).symm
  exact (((hF.1 φ hφ).continuousAt (hU.mem_nhds hφ)).tendsto.comp hψ).congr' he

/-- Uniqueness transfers analyticity from one classical extension to every
other one, using only agreement on the open initial-data neighborhood. -/
theorem IsContinuousClassicalRenormalizedNLSExtensionOn.analytic_of_reference
    {hp : p ≠ ⊤} {hp1 : 1 < p} {T : ℝ} {U : Set (realTypeSourceSubmodule p)}
    {F G : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p)}
    (hF : IsContinuousClassicalRenormalizedNLSExtensionOn hp hp1 T U F)
    (hG : IsContinuousClassicalRenormalizedNLSExtensionOn hp hp1 T U G)
    (hU : IsOpen U) (hA : AnalyticOnNhd ℝ G U) : AnalyticOnNhd ℝ F U := by
  have he := hF.unique hG hU
  intro φ hφ
  apply (hA φ hφ).congr
  filter_upwards [hU.mem_nhds hφ] with ψ hψ
  exact (he hψ).symm

/-- Every continuous classical extension has the original initial value,
including at rough initial sources in its open neighborhood. -/
theorem IsContinuousClassicalRenormalizedNLSExtensionOn.initial_value
    {hp : p ≠ ⊤} {hp1 : 1 < p} {T : ℝ} {U : Set (realTypeSourceSubmodule p)}
    {F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p)}
    (hF : IsContinuousClassicalRenormalizedNLSExtensionOn hp hp1 T U F) (hU : IsOpen U)
    (hT : 0 ≤ T) (φ : realTypeSourceSubmodule p) (hφ : φ ∈ U) :
    F φ ⟨0,by constructor <;> linarith⟩ = φ := by
  let zeroTime : Icc (-T) T := ⟨0,by constructor <;> linarith⟩
  obtain ⟨ψ,hf,hψ⟩ := exists_sourceFiniteGap_sequence hp hp1 φ
  have he : (fun j => F (ψ j) zeroTime) =ᶠ[atTop] ψ := by
    filter_upwards [hψ.eventually (hU.mem_nhds hφ)] with j hj
    apply realTypeSource_eq_of_fst
    intro n
    rw [hF.2 (ψ j) hj (hf j) zeroTime n]
    change periodOneCoefficient (fun x : ℝ => sourceFiniteGapClassicalRenormalizedTrajectory
      hp hp1 (ψ j) (hf j) 0 (x : AddCircle (2 : ℝ))) n = _
    rw [funext (sourceFiniteGapClassicalRenormalizedTrajectory_spec hp hp1 (ψ j) (hf j)).2]
    exact (periodOneCoefficient_sourceFiniteGapPhysicalPair hp hp1 (ψ j) (hf j) n).1
  have hc : Continuous (fun g : C(Icc (-T) T,realTypeSourceSubmodule p) => g zeroTime) :=
    continuous_eval_const zeroTime
  have hlim := hc.continuousAt.tendsto.comp
    (((hF.1 φ hφ).continuousAt (hU.mem_nhds hφ)).tendsto.comp hψ)
  exact tendsto_nhds_unique (hlim.congr' he) hψ

namespace SourceAbelianMomentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P V B X : Set (CoeffPair p)}
variable {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- On every admissible initial-data set, the physical image trajectory is
a continuous extension of actual classical renormalized finite-gap dynamics. -/
theorem isContinuousClassicalRenormalizedNLSExtensionOn_hamiltonianImageTrajectory
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (h2p : 2 ≤ p) (T : ℝ) (U : Set (realTypeSourceSubmodule p))
    (hU : U ⊆ A.renormalizedTrajectoryDomain t T) :
    IsContinuousClassicalRenormalizedNLSExtensionOn hp hp1 T U (A.hamiltonianRenormalizedImageTrajectoryOn D T) := by
  refine ⟨((A.analytic_hamiltonianRenormalizedImageTrajectoryOn hs hP hr D T).mono hU).continuousOn,?_⟩
  intro φ hφ hf time n
  rw [A.hamiltonianRenormalizedImageTrajectoryOn_apply hs hP hr D T φ (hU hφ) time]
  exact A.hamiltonianRenormalizedImageFlow_fst_eq_classical hs.toSourcePsiIsolatingComplexExtension
    D h2p φ hf time.val n

end SourceAbelianMomentAtlas

/-- Every real source at finite p ≥ 2 has an open neighborhood and a common
positive time interval with an analytic classical renormalized extension.
Every continuous classical extension on that neighborhood coincides with it
and is analytic there. All spectral data are constructed internally. -/
theorem exists_local_classicalRenormalizedNLSExtension
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) (φ : realTypeSourceSubmodule p) :
    ∃ T > 0, ∃ U : Set (realTypeSourceSubmodule p), IsOpen U ∧ φ ∈ U ∧
      ∃ F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p),
        AnalyticOnNhd ℝ F U ∧ IsContinuousClassicalRenormalizedNLSExtensionOn hp hp1 T U F ∧
        ∀ G : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p),
          IsContinuousClassicalRenormalizedNLSExtensionOn hp hp1 T U G →
            EqOn G F U ∧ AnalyticOnNhd ℝ G U := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  obtain ⟨T,hT,U,hU,hφ,hsub,_⟩ := A.exists_local_analytic_renormalizedTrajectories hs hP hr D φ
  have ha := (A.analytic_hamiltonianRenormalizedImageTrajectoryOn hs hP hr D T).mono hsub
  have he := A.isContinuousClassicalRenormalizedNLSExtensionOn_hamiltonianImageTrajectory hs hP hr D h2p T U hsub
  exact ⟨T,hT,U,hU,hφ,A.hamiltonianRenormalizedImageTrajectoryOn D T,ha,he,
    fun _ hG => ⟨hG.unique he hU,hG.analytic_of_reference he hU ha⟩⟩

end NLS.ZakharovShabat
