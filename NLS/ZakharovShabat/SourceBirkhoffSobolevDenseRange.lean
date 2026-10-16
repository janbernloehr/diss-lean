import NLS.ZakharovShabat.SourceBirkhoffWeightedContinuity
import NLS.ZakharovShabat.SourceBirkhoffFiniteSupport
import NLS.ZakharovShabat.SourceFiniteGapSobolev

/-! # Dense image in every original real Sobolev target

Finite target truncations have actual finite-gap preimages. Their full Sobolev
regularity gives lifts into every nonnegative real order at the original
exponent. Finite truncations converge in the weighted target norm, so the
original map has dense image for every finite p>1. No open-image, surjectivity,
or arbitrary-spectral-weight density assertion is inferred.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every actual finite-gap source has a lift to the exact original fractional Sobolev source. -/
theorem sourceFiniteGap_exists_originalWeightedRealSource (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight t ht),
      originalWeightedRealSource (sourceSobolevSpectralWeight t ht) a = φ := by
  have hmem := sourceFiniteGap_mem_all_sobolev hp hp1 φ hf t ht
  let w := sourceSobolevSpectralWeight t ht
  let a1 : WeightedCoeff (sourceFrequencyWeight w) p := ⟨φ.val.fst, by
    change Memℓp (fun n => (sourceFrequencyWeight w n : ℂ) * φ.val.fst n) p
    simpa only [w, sourceFrequencyWeight_sobolev] using hmem.1⟩
  let a2 : WeightedCoeff (sourceFrequencyWeight w) p := ⟨φ.val.snd, by
    change Memℓp (fun n => (sourceFrequencyWeight w n : ℂ) * φ.val.snd n) p
    simpa only [w, sourceFrequencyWeight_sobolev] using hmem.2⟩
  let b : WeightedCoeffPair (sourceFrequencyWeight w) p := WithLp.toLp p (a1, a2)
  have hb : b ∈ weightedRealSourceSubmodule w := by
    rw [mem_weightedRealSourceSubmodule_iff]
    exact φ.property
  let a : weightedRealSourceSubmodule (p := p) w := ⟨b, hb⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply (WithLp.equiv p _).injective
  apply Prod.ext <;> apply lp.ext <;> funext n
  · exact originalWeightedRealSource_fst w a n
  · exact originalWeightedRealSource_snd w a n

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Every finite real target truncation is attained by an original source of every positive smoothness. -/
theorem truncatePair_attained_by_sobolev_source (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (t : ℝ) (ht : 0 ≤ t) (A : Finset ℤ) (z : RealCoeff p × RealCoeff p) :
    ∃ a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight t ht),
      sourceRealBirkhoffMap hp hp1 s (originalWeightedRealSource (sourceSobolevSpectralWeight t ht) a) =
        RealCoeff.truncatePair A z := by
  obtain ⟨φ, hφ⟩ := D.truncatePair_mem_real_map_range A z
  obtain ⟨a, ha⟩ := sourceFiniteGap_exists_originalWeightedRealSource hp hp1 φ
    (D.finiteGap_of_real_map_eq_truncatePair φ A z hφ) t ht
  exact ⟨a, ha ▸ hφ⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
open Set Filter Topology
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def finiteUnweight (w : SpectralWeight) (A : Finset ℤ) (a : RealCoeff p) : RealCoeff p :=
  ∑ n ∈ A, lp.single p n (a n / w (2*n))

omit [Fact (1 ≤ p)] in
private theorem finiteUnweight_apply (w : SpectralWeight) (A : Finset ℤ) (a : RealCoeff p) (n : ℤ) :
    finiteUnweight w A a n = if n ∈ A then a n / w (2*n) else 0 := by
  change (lp.evalₗ (𝕜 := ℝ) (fun _ : ℤ => ℝ) p n) (∑ j ∈ A, lp.single p j (a j / w (2*j))) = _
  rw [map_sum]
  simp [lp.evalₗ_apply, lp.single_apply, Pi.single_apply]

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Every finite normalized target truncation is attained at every nonnegative Sobolev order. -/
theorem truncatePair_mem_weightedRealMap_sobolev_range (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (t : ℝ) (ht : 0 ≤ t) (A : Finset ℤ) (z : RealCoeff p × RealCoeff p) :
    WithLp.toLp p (RealCoeff.truncatePair A z) ∈
      range (D.weightedRealMap (sourceSobolevSpectralWeight t ht)) := by
  let w := sourceSobolevSpectralWeight t ht
  let y := (finiteUnweight w A z.1, finiteUnweight w A z.2)
  obtain ⟨a, ha⟩ := D.truncatePair_attained_by_sobolev_source t ht A y
  refine ⟨weightedRealSourceEquiv w a, ?_⟩
  apply (WithLp.equiv p _).injective
  apply Prod.ext <;> apply lp.ext <;> funext n
  · change w (2*n) * (sourceRealBirkhoffMap hp hp1 s (originalWeightedRealSource w a)).1 n = _
    rw [ha]
    by_cases hn : n ∈ A <;>
      simp [y, RealCoeff.truncatePair, RealCoeff.truncate_apply, finiteUnweight_apply, hn,
        mul_div_cancel₀ _ (w.toWeight.positive (2*n)).ne']
  · change w (2*n) * (sourceRealBirkhoffMap hp hp1 s (originalWeightedRealSource w a)).2 n = _
    rw [ha]
    by_cases hn : n ∈ A <;>
      simp [y, RealCoeff.truncatePair, RealCoeff.truncate_apply, finiteUnweight_apply, hn,
        mul_div_cancel₀ _ (w.toWeight.positive (2*n)).ne']

/-- Density in the full weighted target norm, including fractional orders and exponents above two. -/
theorem weightedRealMap_sobolev_denseRange (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (t : ℝ) (ht : 0 ≤ t) : DenseRange (D.weightedRealMap (sourceSobolevSpectralWeight t ht)) := by
  intro z
  have hlim := (WithLp.prod_continuous_toLp p (RealCoeff p) (RealCoeff p)).continuousAt.tendsto.comp
    (RealCoeff.tendsto_truncatePair hp (z.fst, z.snd))
  exact isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall
    (fun A => subset_closure (D.truncatePair_mem_weightedRealMap_sobolev_range t ht A (z.fst, z.snd))))

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
open Set Filter Topology
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The actual original weighted real Birkhoff map has dense range at every Sobolev order. -/
theorem originalWeightedRealMap_sobolev_denseRange (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (t : ℝ) (ht : 0 ≤ t) : DenseRange (D.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) := by
  let w := sourceSobolevSpectralWeight t ht
  have h := (D.weightedRealMap_sobolev_denseRange t ht).comp
    (weightedRealSourceEquiv w).surjective.denseRange (D.weightedRealMap_continuous w)
  exact (weightedRealTargetDecode (sourceFrequencyWeight w)).surjective.denseRange.comp h
    (weightedRealTargetDecode (sourceFrequencyWeight w)).continuous

end SourceBirkhoffMapComplexData

/-- One actual source construction yields continuous injections with dense image on every real Sobolev scale. -/
theorem sourceSection14_weighted_sobolev_continuous_injective_dense (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection14Data hp hp1 W₀ W V s, ∀ t : ℝ, ∀ ht : 0 ≤ t,
        Continuous (D.complex.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) ∧
          Function.Injective (D.complex.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) ∧
          DenseRange (D.complex.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) := by
  obtain ⟨W₀, W, V, s, D⟩ := sourceSection14 hp hp1
  exact ⟨W₀, W, V, s, D, fun t ht =>
    ⟨D.complex.originalWeightedRealMap_continuous _, D.complex.originalWeightedRealMap_injective _,
      D.complex.originalWeightedRealMap_sobolev_denseRange t ht⟩⟩

end NLS.ZakharovShabat
