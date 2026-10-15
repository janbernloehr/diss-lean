import NLS.ZakharovShabat.SourceSection14
import NLS.ZakharovShabat.SourceGapWeightedEtaOriginalSequence
import NLS.ZakharovShabat.SourceGapWeightedEtaOriginalCollapsed

/-!
# Section 15 with the original gap-weighted coordinates

The original angular domain carries the index-uniform estimate and actual
analytic gap-weighted sequences. The compatible Section 14 map retains
equation (3.2), real analyticity, and the three canonical brackets.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Section 15 estimates retain the original domain and the compatible Birkhoff map. -/
structure SourceSection15OriginalData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W₀ W V : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop extends
    SourceSection14Data hp hp1 W₀ W V s where
  gap_bound : ∀ φ ∈ W, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
    ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n : ℤ, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
      ‖sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ‖ ≤ C *
        (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ +
          ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-sourceStandardRootMidpoint hp hp1 ψ n‖)
  sequence_local : ∀ φ ∈ W, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ σ : ℂ, ‖σ‖ ≤ 1 → AnalyticOnNhd ℂ (sourceGapWeightedEtaSequence hp hp1 s σ) U) ∧
      ∀ ψ ∈ U, ∀ σ : ℂ, ‖σ‖ ≤ 1 → ‖sourceGapWeightedEtaSequence hp hp1 s σ ψ‖ ≤ M ∧
        ∀ n : ℤ, sourceGapWeightedEtaSequence hp hp1 s σ ψ n = sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ

namespace SourceSection15OriginalData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Both actual gap-weighted sequences are analytic on the original angular domain. -/
theorem gap_sequence_analytic (D : SourceSection15OriginalData hp hp1 W₀ W V s)
    (σ : ℂ) (hσ : ‖σ‖ ≤ 1) : AnalyticOnNhd ℂ (sourceGapWeightedEtaSequence hp hp1 s σ) W :=
  D.previous.gapWeighted_original_sequence_analytic σ hσ

/-- Equation (3.2) uses actual sequence entries, with a difference in the y-coordinate. -/
theorem equation3_2 (D : SourceSection15OriginalData hp hp1 W₀ W V s)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    let ξ := sourceNormalizedActionRoot hp hp1 n ψ
    let β := sourceAngularBetaCorrection hp hp1 n s ψ
    let zp := sourceGapWeightedEtaSequence hp hp1 s 1 ψ n
    let zm := sourceGapWeightedEtaSequence hp hp1 s (-1) ψ n
    (sourceBirkhoffMap hp hp1 s ψ).1 n = ξ/(Real.sqrt 8 : ℂ)*(zp*Complex.exp (I*β)+zm*Complex.exp (-I*β)) ∧
      (sourceBirkhoffMap hp hp1 s ψ).2 n = ξ/((Real.sqrt 8 : ℂ)*I)*(zp*Complex.exp (I*β)-zm*Complex.exp (-I*β)) := by
  dsimp only
  rw [D.previous.gapWeighted_original_sequence_apply ψ (D.complex.source_subset hψ) 1 (by norm_num) n,
    D.previous.gapWeighted_original_sequence_apply ψ (D.complex.source_subset hψ) (-1) (by norm_num) n,
    (D.complex.coordinates ψ hψ n).1,(D.complex.coordinates ψ hψ n).2,
    sourceBirkhoffX,sourceBirkhoffY,sourceBirkhoffWeightedCoordinate,sourceBirkhoffWeightedCoordinate]
  simp only [one_mul,neg_mul]
  constructor <;> ring

/-- Theorem 15.2: the real map and its actual complex sequence extension are analytic. -/
theorem theorem15_2 (D : SourceSection15OriginalData hp hp1 W₀ W V s) :
    AnalyticOnNhd ℝ (sourceRealBirkhoffMap hp hp1 s) univ ∧
    AnalyticOnNhd ℂ (sourceBirkhoffMap hp hp1 s) V ∧
    ∀ φ : realTypeSourceSubmodule p,
      ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p))
        (sourceRealBirkhoffMap hp hp1 s φ) = sourceBirkhoffMap hp hp1 s φ.val :=
  ⟨D.complex.real_map_analytic,D.complex.analytic,D.complex.real_map_complex_inclusion⟩

/-- Lemma 15.3 for the same original family, with actual coordinate derivatives. -/
theorem lemma15_3 (D : SourceSection15OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) :
    ∃ X Y : ℤ → RegularSourceCotangent p,
      (∀ n, (X n).toCotangent = fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ.val ∧
        (Y n).toCotangent = fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val) ∧
      ∀ n m, (X n).bivector (X m) = 0 ∧
        (X n).bivector (Y m) = -(if n = m then 1 else 0) ∧ (Y n).bivector (Y m) = 0 :=
  D.complex.lemma15_3 φ

end SourceSection15OriginalData

/-- Construct Section 15 with the original domain, actual sequences, and compatible map. -/
theorem sourceSection15_original (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourceSection15OriginalData hp hp1 W₀ W V s := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 hp hp1
  exact ⟨W₀,W,V,s,D,D.previous.gapWeighted_original_uniform_bound,D.previous.gapWeighted_original_local_sequence⟩

end NLS.ZakharovShabat
