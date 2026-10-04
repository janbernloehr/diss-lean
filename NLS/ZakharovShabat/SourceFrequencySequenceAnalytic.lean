import NLS.ZakharovShabat.SourceFrequencySequenceBounds
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Analytic frequency maps in sequence spaces

Scalar moment analyticity and the locally uniform sequence bounds combine
on one connected neighborhood, common to all admissible target exponents.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual frequency map is analytic in every finite lr above one
and at least p/2. Its refined correction bounds hold on the same domain. -/
theorem exists_analytic_frequencySequence
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
        ENNReal.ofReal (p.toReal/2) ≤ r →
        (∀ ψ ∈ U, ∀ n, A.frequencySequence r ψ n = A.renormalizedFrequency n ψ) ∧
          AnalyticOnNhd ℂ (A.frequencySequence r) U) ∧
      ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
            (∀ n, b n = A.frequencyCorrection ψ n) ∧ ‖b‖ ≤ C := by
  obtain ⟨B,hB,_,hrealB,hBV,hcorr,hbound⟩ :=
    A.exists_frequencySequence_neighborhood hs hV hrealV
  obtain ⟨D,hD,_,hrealD,_,_,hscalar,_⟩ :=
    A.exists_analytic_renormalizedFrequency hs hV hrealV
  let U := connectedComponentIn (B ∩ D) (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by
    exact (realTypeSourceSubmodule p).zero_mem
  have hrealBD : realTypeSourceLocus p ⊆ B ∩ D := fun ψ hψ => ⟨hrealB hψ,hrealD hψ⟩
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealBD
  have hUBD : U ⊆ B ∩ D := connectedComponentIn_subset _ _
  have hU : IsOpen U := (hB.inter hD).connectedComponentIn
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hrealBD hzero),hrealU,
    fun ψ hψ => hBV (hUBD hψ).1,?_,?_⟩
  · intro r inst hr hr1 hpr
    have he (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) :
        A.frequencySequence r ψ n = A.renormalizedFrequency n ψ := by
      obtain ⟨T,_,hψT,_,hb⟩ := hbound ψ (hUBD hψ).1
      obtain ⟨_,_,hb⟩ := hb r hr hr1 hpr
      exact (hb ψ hψT).1 n
    refine ⟨he,?_⟩
    intro φ hφ
    obtain ⟨T,hT,hφT,_,hb⟩ := hbound φ (hUBD hφ).1
    obtain ⟨C,_,hb⟩ := hb r hr hr1 hpr
    have hcoord (n : ℤ) : AnalyticOnNhd ℂ (fun ψ => A.frequencySequence r ψ n) (T ∩ U) := by
      intro ψ hψ
      apply (hscalar n ψ (hUBD hψ.2).2).congr
      filter_upwards [hU.mem_nhds hψ.2] with x hx
      exact (he x hx n).symm
    exact Coeff.analyticOnNhd_of_bounded_coordinatewise (A.frequencySequence r)
      (hT.inter hU) hcoord C (fun ψ hψ => (hb ψ hψ.1).2) φ ⟨hφT,hφ⟩
  · intro φ hφ
    obtain ⟨T,hT,hφT,_,hc⟩ := hcorr φ (hUBD hφ).1
    refine ⟨T ∩ U,hT.inter hU,⟨hφT,hφ⟩,fun _ h => h.2,?_⟩
    intro r hr hr1 hpr
    obtain ⟨C,hC,hc⟩ := hc r hr hr1 hpr
    exact ⟨C,hC,fun ψ hψ => hc ψ hψ.1⟩

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
