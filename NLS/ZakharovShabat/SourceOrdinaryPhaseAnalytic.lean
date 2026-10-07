import NLS.ZakharovShabat.SourceOrdinaryFlowTrajectories
import NLS.ZakharovShabat.SourceRenormalizedPhaseAnalytic

/-! # Analytic ordinary NLS coordinate trajectories

Adding the entire physical mass as a constant bounded symbol gives the
ordinary phase correction. The complete compact-time coordinate map has
a complex analytic extension on one common neighborhood of the real locus.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The ordinary correction includes the constant mass symbol. -/
def ordinaryBoundedCorrection (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hp2 : p ≤ 2) (φ : CoeffPair p) : Coeff ⊤ :=
  A.boundedPhaseCorrection φ + (4*sourceOrdinaryComplexMass hp2 φ) • (1 : Coeff ⊤)

/-- Complex extension of the ordinary coordinate path. -/
def ordinaryComplexTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (hp2 : p ≤ 2) (T : ℝ) (φ : CoeffPair p) :
    C(Icc (-T) T,Coeff p × Coeff p) :=
  Birkhoff.analyticPhaseTrajectory hp (fun n : ℤ => (2*Real.pi*n)^2)
    ⟨Subtype.val,continuous_subtype_val⟩ (A.ordinaryBoundedCorrection hp2 φ)
    (sourceComplexBirkhoffMap hp hp1 t φ)

/-- One common complex neighborhood supports every compact-time ordinary trajectory map. -/
theorem exists_analytic_ordinaryComplexTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧
      (∀ T : ℝ, AnalyticOnNhd ℂ (A.ordinaryComplexTrajectoryOn t hp2 T) U) ∧
      ∀ T : ℝ, ∀ φ : realTypeSourceSubmodule p,
        A.ordinaryComplexTrajectoryOn t hp2 T φ.val = A.ordinaryPhaseTrajectoryOn hs hP hr D hp2 T φ := by
  obtain ⟨V,hV,hrV,_,ha,he⟩ := A.exists_analytic_boundedPhaseCorrection hs hP hr
  have hb : AnalyticOnNhd ℂ (A.ordinaryBoundedCorrection hp2) V := by
    intro φ hφ
    exact (ha φ hφ).add ((analyticAt_const.mul
      (analytic_sourceOrdinaryComplexMass hp2 φ (mem_univ _))).smul analyticAt_const)
  have hbval (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ) :
      A.ordinaryBoundedCorrection hp2 φ n =
        A.renormalizedFrequency n φ + 4*sourceOrdinaryComplexMass hp2 φ := by
    change A.boundedPhaseCorrection φ n + (4*sourceOrdinaryComplexMass hp2 φ)*1 = _
    rw [he φ hφ n,mul_one]
  refine ⟨V ∩ X,hV.inter D.source_open,fun φ hφ => ⟨hrV hφ,D.real_subset hφ⟩,?_,?_⟩
  · intro T φ hφ
    exact (Birkhoff.analyticAt_analyticPhaseTrajectory hp (fun n : ℤ => (2*Real.pi*n)^2)
      (⟨Subtype.val,continuous_subtype_val⟩ : C(Icc (-T) T,ℝ))
      (A.ordinaryBoundedCorrection hp2 φ,sourceComplexBirkhoffMap hp hp1 t φ)).comp
      (f := fun ψ => (A.ordinaryBoundedCorrection hp2 ψ,sourceComplexBirkhoffMap hp hp1 t ψ))
      ((hb φ hφ.1).prod (D.complex_map_analytic φ hφ.2))
  · intro T φ
    apply ContinuousMap.ext
    intro τ
    apply Prod.ext <;> ext n
    · rw [ordinaryComplexTrajectoryOn,Birkhoff.analyticPhaseTrajectory_fst,hbval φ.val (hrV φ.property)]
      change _ = (A.ordinaryPhaseTrajectory t hp2 φ τ.val).1 n
      rw [A.ordinaryPhaseTrajectory_fst hs.toSourcePsiIsolatingComplexExtension]
      dsimp only [ContinuousMap.coe_mk]
      push_cast
      congr 2
      ring
    · rw [ordinaryComplexTrajectoryOn,Birkhoff.analyticPhaseTrajectory_snd,hbval φ.val (hrV φ.property)]
      change _ = (A.ordinaryPhaseTrajectory t hp2 φ τ.val).2 n
      rw [A.ordinaryPhaseTrajectory_snd hs.toSourcePsiIsolatingComplexExtension]
      dsimp only [ContinuousMap.coe_mk]
      push_cast
      congr 2
      ring

/-- Real analytic dependence in the full uniform coordinate trajectory norm. -/
theorem analytic_ordinaryPhaseTrajectoryOn (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (hp2 : p ≤ 2) (T : ℝ) : AnalyticOnNhd ℝ (A.ordinaryPhaseTrajectoryOn hs hP hr D hp2 T) univ := by
  obtain ⟨U,_,hrU,ha,he⟩ := A.exists_analytic_ordinaryComplexTrajectoryOn hs hP hr D hp2
  intro φ _
  have h := ((ha T φ.val (hrU φ.property)).restrictScalars (𝕜 := ℝ)).comp
    ((realTypeSourceSubmodule p).subtypeL.analyticAt (𝕜 := ℝ) (x := φ))
  simpa only [Function.comp_def,he] using! h

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
