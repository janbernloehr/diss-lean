import NLS.ComplexAnalysis.BanachHolomorphicAffineLineTaylor
import NLS.ZakharovShabat.SourceNormalizedActionComplexSequenceDerivative
import NLS.ZakharovShabat.SourceNormalizedActionRootSequenceSpace

/-!
# Banach-valued Taylor series along complex source lines

The normalized-action and principal-root deviations take values in
`ℓq` on local complex neighborhoods. Along every sufficiently short
complex affine line, their `ℓq`-valued Cauchy series converge at the
endpoint of the line.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every short complex line through a nearby source has a convergent
`ℓq`-valued Taylor series for the normalized-action deviation. -/
theorem exists_local_sourceNormalizedActionDeviation_affineLineTaylor
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ F : CoeffPair p → Coeff q,
        (∀ ψ ∈ V, ∀ n : ℤ,
          F ψ n = sourceNormalizedActionDeviation hp hp1 ψ n) ∧
        ∀ ψ ∈ V, ∃ R : ℝ, 0 < R ∧ ball ψ R ⊆ V ∧
          ∀ h : CoeffPair p, ‖h‖ < R/3 →
            let g : ℂ → Coeff q := fun z => F (ψ+z • h)
            ∃ P : FormalMultilinearSeries ℂ ℂ (Coeff q),
              HasFPowerSeriesOnBall g P 0 (2 : ℝ≥0) ∧
              P 1 (fun _ : Fin 1 => 1) = (fderiv ℂ F ψ) h ∧
              HasSum (fun n : ℕ => P n (fun _ : Fin n => 1)) (F (ψ+h)) := by
  obtain ⟨V,hVopen,hφV,F,hFapply,hFdiff,_,_,_⟩ :=
    exists_local_sourceNormalizedActionDeviation_coordinateDerivative
      hp hp1 hq1 hq hhalf φ hreal
  refine ⟨V,hVopen,hφV,F,hFapply,?_⟩
  intro ψ hψ
  exact NLS.ComplexAnalysis.exists_local_affineLine_cauchyTaylor F hVopen hFdiff ψ hψ

/-- The principal normalized-action root deviation has an `ℓq`-valued
Taylor series along every sufficiently short complex source line. -/
theorem exists_local_sourceNormalizedActionRootDeviation_affineLineTaylor
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ F : CoeffPair p → Coeff q,
        (∀ ψ ∈ V, ∀ n : ℤ,
          F ψ n = sourceNormalizedActionRootDeviation hp hp1 ψ n) ∧
        ∀ ψ ∈ V, ∃ R : ℝ, 0 < R ∧ ball ψ R ⊆ V ∧
          ∀ h : CoeffPair p, ‖h‖ < R/3 →
            let g : ℂ → Coeff q := fun z => F (ψ+z • h)
            ∃ P : FormalMultilinearSeries ℂ ℂ (Coeff q),
              HasFPowerSeriesOnBall g P 0 (2 : ℝ≥0) ∧
              P 1 (fun _ : Fin 1 => 1) = (fderiv ℂ F ψ) h ∧
              HasSum (fun n : ℕ => P n (fun _ : Fin n => 1)) (F (ψ+h)) := by
  obtain ⟨V,hVopen,hφV,_,F,hFapply,_,_,hFdiff⟩ :=
    exists_local_sourceNormalizedActionRootDeviation_continuousMap
      hp hp1 hq1 hq hhalf φ hreal
  refine ⟨V,hVopen,hφV,F,hFapply,?_⟩
  intro ψ hψ
  exact NLS.ComplexAnalysis.exists_local_affineLine_cauchyTaylor F hVopen hFdiff ψ hψ

end NLS.ZakharovShabat
