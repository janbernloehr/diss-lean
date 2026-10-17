import NLS.ZakharovShabat.SourceBirkhoffSobolevRegularity
import NLS.ZakharovShabat.SourceBirkhoffSobolevDenseRange
import NLS.ZakharovShabat.SourceBirkhoffGlobalInverse
import NLS.ZakharovShabat.SourceBirkhoffWeightedExponent

/-! # Exact range and bijectivity on original Sobolev spaces

A weighted target is attained precisely when its unweighted image is.
The range is therefore open for every finite p>1 and is the whole target
for 1<p<=2. The bijection and both inverse identities use native weighted
spaces. No continuity or analyticity of its weighted inverse is inferred.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The original weighted map commutes with coefficient-preserving source and target inclusions. -/
theorem originalWeightedRealTarget_map (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (a : weightedRealSourceSubmodule (p := p) w) :
    originalWeightedRealTarget w (D.originalWeightedRealMap w a) =
      sourceRealBirkhoffMap hp hp1 s (originalWeightedRealSource w a) := by
  apply Prod.ext <;> apply lp.ext <;> funext n
  · apply Complex.ofReal_injective
    rw [originalWeightedRealTarget_fst,originalWeightedRealMap_fst]
  · apply Complex.ofReal_injective
    rw [originalWeightedRealTarget_snd,originalWeightedRealMap_snd]

/-- Exact range characterization, including arbitrary targets and exponents above two. -/
theorem originalWeightedRealMap_sobolev_range (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (t : ℝ) (ht : 0 ≤ t) :
    range (D.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) =
      originalWeightedRealTarget (sourceSobolevSpectralWeight t ht) ⁻¹'
        range (sourceRealBirkhoffMap hp hp1 s) := by
  let w := sourceSobolevSpectralWeight t ht
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨originalWeightedRealSource w a,(D.originalWeightedRealTarget_map w a).symm⟩
  · rintro ⟨φ,hφ⟩
    have hm : Memℓp (fun n : ℤ => Weight.sobolev t n*(sourceRealBirkhoffMap hp hp1 s φ).1 n) p ∧
        Memℓp (fun n : ℤ => Weight.sobolev t n*(sourceRealBirkhoffMap hp hp1 s φ).2 n) p := by
      rw [hφ]
      simpa only [w,sourceSobolevSpectralWeight_even] using originalWeightedRealTarget_mem w z
    obtain ⟨a,ha⟩ := (D.exists_originalWeightedRealSource_iff_real_map_mem φ t ht).mpr hm
    refine ⟨a,?_⟩
    apply originalWeightedRealTarget_injective w
    rw [D.originalWeightedRealTarget_map,ha,hφ]

/-- Sobolev restriction preserves the original open-image assertion. -/
theorem originalWeightedRealMap_sobolev_isOpen_range (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (t : ℝ) (ht : 0 ≤ t) :
    IsOpen (range (D.originalWeightedRealMap (sourceSobolevSpectralWeight t ht))) := by
  rw [D.originalWeightedRealMap_sobolev_range t ht]
  exact D.real_map_open_dense_range.1.preimage (originalWeightedRealTarget _).continuous

/-- Every original Sobolev target has a Sobolev source at the same exponent when 1<p<=2. -/
theorem originalWeightedRealMap_sobolev_surjective (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    Function.Surjective (D.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) := by
  intro z
  change z ∈ range (D.originalWeightedRealMap (sourceSobolevSpectralWeight t ht))
  rw [D.originalWeightedRealMap_sobolev_range t ht]
  exact D.proposition17_3 hp2 _

/-- The original map is a bijection of the native Sobolev spaces in the known onto range. -/
theorem originalWeightedRealMap_sobolev_bijective (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    Function.Bijective (D.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) :=
  ⟨D.originalWeightedRealMap_injective _,D.originalWeightedRealMap_sobolev_surjective hp2 t ht⟩

/-- The native Sobolev bijection, with both exact inverse identities. -/
def originalWeightedRealSobolevEquiv (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight t ht) ≃
      WithLp p (WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p ×
        WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p) :=
  Equiv.ofBijective _ (D.originalWeightedRealMap_sobolev_bijective hp2 t ht)

@[simp] theorem originalWeightedRealSobolevEquiv_apply (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight t ht)) :
    D.originalWeightedRealSobolevEquiv hp2 t ht a =
      D.originalWeightedRealMap (sourceSobolevSpectralWeight t ht) a := rfl

/-- The weighted inverse is exactly the original unweighted inverse on raw source coefficients. -/
theorem originalWeightedRealSource_sobolevEquiv_symm
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t)
    (z : WithLp p (WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p ×
      WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p)) :
    originalWeightedRealSource (sourceSobolevSpectralWeight t ht)
      ((D.originalWeightedRealSobolevEquiv hp2 t ht).symm z) =
        (D.realHomeomorph hp2).symm (originalWeightedRealTarget (sourceSobolevSpectralWeight t ht) z) := by
  apply (D.realHomeomorph hp2).injective
  rw [(D.realHomeomorph hp2).apply_symm_apply]
  change sourceRealBirkhoffMap hp hp1 s _ = _
  rw [← D.originalWeightedRealTarget_map]
  exact congrArg (originalWeightedRealTarget (sourceSobolevSpectralWeight t ht))
    ((D.originalWeightedRealSobolevEquiv hp2 t ht).apply_symm_apply z)

/-- The native weighted inverses commute with exponent inclusion, even for independent families. -/
theorem originalWeightedRealSobolevEquiv_symm_exponent
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {hq : q ≠ ⊤} {hq1 : 1 < q}
    {V₀ C V : Set (CoeffPair q)} {u : (k : ℤ) → CoeffPair q → DeletedCoeff q k}
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (E : SourceBirkhoffMapComplexData hq hq1 V₀ C V u)
    (hpq : p ≤ q) (hp2 : p ≤ 2) (hq2 : q ≤ 2) (t : ℝ) (ht : 0 ≤ t)
    (z : WithLp p (WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p ×
      WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p)) :
    weightedRealSourceExponentInclusion (sourceSobolevSpectralWeight t ht) hpq
      ((D.originalWeightedRealSobolevEquiv hp2 t ht).symm z) =
        (E.originalWeightedRealSobolevEquiv hq2 t ht).symm
          (WeightedRealCoeff.pairExponentInclusion (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) hpq z) := by
  let w := sourceSobolevSpectralWeight t ht
  apply (E.originalWeightedRealSobolevEquiv hq2 t ht).injective
  rw [(E.originalWeightedRealSobolevEquiv hq2 t ht).apply_symm_apply]
  change E.originalWeightedRealMap w _ = _
  rw [← D.originalWeightedRealMap_exponent E w hpq]
  exact congrArg (WeightedRealCoeff.pairExponentInclusion (sourceFrequencyWeight w) hpq)
    ((D.originalWeightedRealSobolevEquiv hp2 t ht).apply_symm_apply z)

end SourceBirkhoffMapComplexData

/-- One actual Section 14 package has continuous injections with open dense Sobolev image. -/
theorem sourceSection14_sobolev_open_dense (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection14Data hp hp1 W₀ W V s, ∀ t : ℝ, ∀ ht : 0 ≤ t,
        Continuous (D.complex.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) ∧
          Function.Injective (D.complex.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) ∧
          IsOpen (range (D.complex.originalWeightedRealMap (sourceSobolevSpectralWeight t ht))) ∧
          DenseRange (D.complex.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 hp hp1
  exact ⟨W₀,W,V,s,D,fun t ht =>
    ⟨D.complex.originalWeightedRealMap_continuous _,D.complex.originalWeightedRealMap_injective _,
      D.complex.originalWeightedRealMap_sobolev_isOpen_range t ht,
      D.complex.originalWeightedRealMap_sobolev_denseRange t ht⟩⟩

/-- One actual Section 14 package gives continuous Sobolev bijections for all real orders t>=0. -/
theorem sourceSection14_sobolev_continuous_bijective (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection14Data hp hp1 W₀ W V s, ∀ t : ℝ, ∀ ht : 0 ≤ t,
        Continuous (D.complex.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) ∧
          Function.Bijective (D.complex.originalWeightedRealMap (sourceSobolevSpectralWeight t ht)) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 hp hp1
  exact ⟨W₀,W,V,s,D,fun t ht =>
    ⟨D.complex.originalWeightedRealMap_continuous _,D.complex.originalWeightedRealMap_sobolev_bijective hp2 t ht⟩⟩

end NLS.ZakharovShabat
