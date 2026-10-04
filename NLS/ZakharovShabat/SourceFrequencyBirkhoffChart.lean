import NLS.ZakharovShabat.SourceBirkhoffInverseChart
import NLS.ZakharovShabat.SourceFrequencyActionInvariance
import NLS.ZakharovShabat.SourceActionCorrectionBounds

/-! # Frequency maps in real-compatible complex Birkhoff charts

One chart at each real source supports every admissible frequency target
and every refined correction target. On the real slice these maps are
constant on quadratic action fibers. Analytic descent through the
quadratic map, particularly at zero coordinates, remains a separate step.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B X W P U : Set (CoeffPair p)}
  {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t}
  {φ : realTypeSourceSubmodule p}

namespace SourceBirkhoffInverseChart

/-- The literal frequency sequence is constant on real quadratic action fibers. -/
theorem frequency_eq_of_pairAction
    (C : SourceBirkhoffInverseChart D φ U) (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (z w : RealCoeff p × RealCoeff p)
    (hz : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z ∈ C.target)
    (hw : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) w ∈ C.target)
    (he : ∀ n, RealCoeff.pairAction w n = RealCoeff.pairAction z n) (r : ℝ≥0∞) :
    A.frequencySequence r (C.realInverse w hw).val =
      A.frequencySequence r (C.realInverse z hz).val :=
  A.frequencySequence_real_eq_of_actions A hs hs _ _
    (C.realInverse_mem_actionLevelSet z w hz hw he) r

/-- The refined correction has the same quadratic action invariance. -/
theorem actionCorrection_eq_of_pairAction
    (C : SourceBirkhoffInverseChart D φ U) (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (z w : RealCoeff p × RealCoeff p)
    (hz : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z ∈ C.target)
    (hw : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) w ∈ C.target)
    (he : ∀ n, RealCoeff.pairAction w n = RealCoeff.pairAction z n) (r : ℝ≥0∞) :
    A.actionFrequencyCorrectionSequence r (C.realInverse w hw).val =
      A.actionFrequencyCorrectionSequence r (C.realInverse z hz).val :=
  A.actionFrequencyCorrectionSequence_real_eq_of_actions A hs hs _ _
    (C.realInverse_mem_actionLevelSet z w hz hw he) r

end SourceBirkhoffInverseChart

/-- Construct the actual atlas and Birkhoff family together with a common
chart for all analytic targets at each real source. The refined correction
coordinates are frequency plus twice the quadratic actions. -/
theorem exists_sourceFrequency_boundedBirkhoffCharts (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W P : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
        SourcePsiIsolatingComplexExtension hp hp1 P s ∧
        A.HasLocallyUniformActionCorrectionBounds ∧
        ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
          ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
          ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ A.domain ∧
            ∀ φ : realTypeSourceSubmodule p, ∃ C : SourceBirkhoffInverseChart D φ U,
              (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
                ENNReal.ofReal (p.toReal/2) ≤ r →
                AnalyticOnNhd ℂ (A.frequencySequence r ∘ C.inverse) C.target ∧
                ∀ z ∈ C.target, ∀ n,
                  A.frequencySequence r (C.inverse z) n = A.renormalizedFrequency n (C.inverse z)) ∧
              (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
                ENNReal.ofReal (p.toReal/3) ≤ r →
                AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) C.target ∧
                ∀ z ∈ C.target, ∀ n,
                  A.actionFrequencyCorrectionSequence r (C.inverse z) n =
                    A.renormalizedFrequency n (C.inverse z) + z.1 n ^ 2 + z.2 n ^ 2) ∧
              ∀ (z w : RealCoeff p × RealCoeff p)
                (hz : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z ∈ C.target)
                (hw : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) w ∈ C.target),
                (∀ n, RealCoeff.pairAction w n = RealCoeff.pairAction z n) →
                ∀ r : ℝ≥0∞,
                  A.frequencySequence r (C.realInverse w hw).val =
                    A.frequencySequence r (C.realInverse z hz).val ∧
                  A.actionFrequencyCorrectionSequence r (C.realInverse w hw).val =
                    A.actionFrequencyCorrectionSequence r (C.realInverse z hz).val := by
  obtain ⟨W,P,_,_,hP,hrealP,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨V,hV,_,hrealV,hVP,hfreq,_⟩ := A.exists_analytic_frequencySequence hs hP hrealP
  obtain ⟨T,hT,_,hrealT,_,hcorr,hlocal⟩ :=
    A.exists_actionFrequencyCorrection_neighborhood hs hP hrealP
  have hbounds : A.HasLocallyUniformActionCorrectionBounds := by
    intro φ
    obtain ⟨S,hS,hφS,_,hb⟩ := hlocal φ.val (hrealT φ.property)
    exact ⟨S,hS,hφS,hb⟩
  obtain ⟨W₀,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  refine ⟨W,P,s,A,hs.toSourcePsiIsolatingComplexExtension,hbounds,W₀,B,X,t,D,V ∩ T,
    hV.inter hT,fun ψ hψ => ⟨hrealV hψ,hrealT hψ⟩,fun ψ hψ => (hVP hψ.1).1,?_⟩
  intro φ
  obtain ⟨C⟩ := D.exists_inverseChart φ (V ∩ T) (hV.inter hT) ⟨hrealV φ.property,hrealT φ.property⟩
  refine ⟨C,?_,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨he,ha⟩ := hfreq r hr hr1 hpr
    exact ⟨C.analytic_comp _ (ha.mono inter_subset_left),
      fun z hz n => he _ (C.image_subset hz).2.1 n⟩
  · intro r inst hr hr1 hpr
    obtain ⟨he,ha⟩ := Coeff.analytic_realization_of_local_bounds
      A.actionFrequencyCorrection hT hcorr (by
        intro ψ hψ
        obtain ⟨S,hS,hψS,hST,hb⟩ := hlocal ψ hψ
        obtain ⟨M,_,hb⟩ := hb r hr hr1 hpr
        exact ⟨S,hS,hψS,hST,M,hb⟩)
    refine ⟨C.analytic_comp _ (ha.mono inter_subset_right),?_⟩
    intro z hz n
    change Coeff.ofFunctionOrZero r (A.actionFrequencyCorrection (C.inverse z)) n = _
    rw [he _ (C.image_subset hz).2.2 n,
      SourceAbelianMomentAtlas.actionFrequencyCorrection,C.action_eq z hz n]
    ring
  · intro z w hz hw he r
    exact ⟨C.frequency_eq_of_pairAction A hs.toSourcePsiIsolatingComplexExtension z w hz hw he r,
      C.actionCorrection_eq_of_pairAction A hs.toSourcePsiIsolatingComplexExtension z w hz hw he r⟩

/-- The original chart interface, omitting the retained uniform source bounds. -/
theorem exists_sourceFrequency_birkhoffCharts (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W P : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
        SourcePsiIsolatingComplexExtension hp hp1 P s ∧
        ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
          ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
          ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ A.domain ∧
            ∀ φ : realTypeSourceSubmodule p, ∃ C : SourceBirkhoffInverseChart D φ U,
              (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
                ENNReal.ofReal (p.toReal/2) ≤ r →
                AnalyticOnNhd ℂ (A.frequencySequence r ∘ C.inverse) C.target ∧
                ∀ z ∈ C.target, ∀ n,
                  A.frequencySequence r (C.inverse z) n = A.renormalizedFrequency n (C.inverse z)) ∧
              (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
                ENNReal.ofReal (p.toReal/3) ≤ r →
                AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) C.target ∧
                ∀ z ∈ C.target, ∀ n,
                  A.actionFrequencyCorrectionSequence r (C.inverse z) n =
                    A.renormalizedFrequency n (C.inverse z) + z.1 n ^ 2 + z.2 n ^ 2) ∧
              ∀ (z w : RealCoeff p × RealCoeff p)
                (hz : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z ∈ C.target)
                (hw : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) w ∈ C.target),
                (∀ n, RealCoeff.pairAction w n = RealCoeff.pairAction z n) →
                ∀ r : ℝ≥0∞,
                  A.frequencySequence r (C.realInverse w hw).val =
                    A.frequencySequence r (C.realInverse z hz).val ∧
                  A.actionFrequencyCorrectionSequence r (C.realInverse w hw).val =
                    A.actionFrequencyCorrectionSequence r (C.realInverse z hz).val := by
  obtain ⟨W,P,s,A,hs,hbounds,hrest⟩ := exists_sourceFrequency_boundedBirkhoffCharts hp hp1
  exact ⟨W,P,s,A,hs,hrest⟩

end NLS.ZakharovShabat
