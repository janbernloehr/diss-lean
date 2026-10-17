import NLS.ZakharovShabat.SourceWeightedComplexExponent
import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexDomain
import NLS.ZakharovShabat.SourceSection14

/-! # Weighted Birkhoff maps on full complex exponent intersections

The original unweighted identities and injectivity of the raw target
inclusion identify the whole weighted sequence and its full derivative.
No common root-family, reality, or open-gap hypothesis is imposed.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {hq : q ≠ ⊤} {hq1 : 1 < q} {A C V : Set (CoeffPair q)}
  {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}

private theorem eventually_in_two_domains
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (J : E → F) (hJ : Continuous J) (U : Set E) (V : Set F)
    (hU : IsOpen U) (hV : IsOpen V) (a : E) (ha : a ∈ U) (ha' : J a ∈ V) :
    ∀ᶠ b in 𝓝 a, b ∈ U ∧ J b ∈ V := by
  filter_upwards [hU.mem_nhds ha,
    hJ.continuousAt.preimage_mem_nhds (hV.mem_nhds ha')] with b hb hb'
  exact ⟨hb,hb'⟩

/-- Exact sequence equality on the whole complex overlap, for independent families. -/
theorem SourceSection14Data.weighted_complex_exponent
    (D : SourceSection14Data hp hp1 W₀ B W s) (E : SourceSection14Data hq hq1 A C V t)
    (w : SpectralWeight) (hpq : p ≤ q)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p)
    (ha : a ∈ D.complex.originalWeightedComplexDomain w)
    (ha' : WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a ∈ E.complex.originalWeightedComplexDomain w) :
    WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq (originalWeightedBirkhoffMap hp hp1 s w a) =
      originalWeightedBirkhoffMap hq hq1 t w (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a) := by
  have hd := (D.complex.originalWeightedComplexDomain_spec w).2.2.2 a ha
  have he := (E.complex.originalWeightedComplexDomain_spec w).2.2.2 _ ha'
  apply weightedBirkhoffTargetInclusion_injective w
  rw [weightedBirkhoffTargetInclusion_exponent,hd.2.1,he.2.1,originalWeightedSourceCLM_exponent]
  exact D.exponent E hpq _ hd.1 (by simpa only [originalWeightedSourceCLM_exponent] using he.1)

/-- The full bounded weighted derivatives commute with exponent inclusion. -/
theorem SourceSection14Data.weighted_complex_fderiv_exponent
    (D : SourceSection14Data hp hp1 W₀ B W s) (E : SourceSection14Data hq hq1 A C V t)
    (w : SpectralWeight) (hpq : p ≤ q)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p)
    (ha : a ∈ D.complex.originalWeightedComplexDomain w)
    (ha' : WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a ∈ E.complex.originalWeightedComplexDomain w) :
    (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq).comp
      (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a) =
        (fderiv ℂ (originalWeightedBirkhoffMap hq hq1 t w)
          (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a)).comp
          (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq) := by
  have hd := (D.complex.originalWeightedComplexDomain_spec w).2.2.2 a ha
  have he := (E.complex.originalWeightedComplexDomain_spec w).2.2.2 _ ha'
  have hu := D.fderiv_exponent E hpq (originalWeightedSourceCLM w a) hd.1
    (by simpa only [originalWeightedSourceCLM_exponent] using he.1)
  apply ContinuousLinearMap.ext
  intro v
  change WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq
      (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a v) =
    fderiv ℂ (originalWeightedBirkhoffMap hq hq1 t w)
      (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a)
      (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq v)
  apply weightedBirkhoffTargetInclusion_injective w
  have hdv := congrArg (fun L => L v) hd.2.2
  have hev := congrArg (fun L => L (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq v)) he.2.2
  have huv := congrArg (fun L => L (originalWeightedSourceCLM w v)) hu
  simp only [ContinuousLinearMap.comp_apply] at hdv hev huv
  rw [weightedBirkhoffTargetInclusion_exponent,hdv,huv,hev,
    originalWeightedSourceCLM_exponent,originalWeightedSourceCLM_exponent]

/-- One common complex germ identifies the entire weighted sequence at each overlap point. -/
theorem SourceSection14Data.eventually_weighted_complex_exponent
    (D : SourceSection14Data hp hp1 W₀ B W s) (E : SourceSection14Data hq hq1 A C V t)
    (w : SpectralWeight) (hpq : p ≤ q)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p)
    (ha : a ∈ D.complex.originalWeightedComplexDomain w)
    (ha' : WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a ∈ E.complex.originalWeightedComplexDomain w) :
    (fun b => WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq
      (originalWeightedBirkhoffMap hp hp1 s w b)) =ᶠ[𝓝 a]
        (fun b => originalWeightedBirkhoffMap hq hq1 t w
          (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq b)) := by
  have h := eventually_in_two_domains
    (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq)
    (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq).continuous
    _ _ (D.complex.originalWeightedComplexDomain_spec w).1
    (E.complex.originalWeightedComplexDomain_spec w).1 a ha ha'
  filter_upwards [h] with b hb
  exact D.weighted_complex_exponent E w hpq b hb.1 hb.2

/-- At equal exponents the original complex weighted map is independent of the chosen family. -/
theorem SourceSection14Data.weighted_complex_family_independent
    (D : SourceSection14Data hp hp1 W₀ B W s)
    {A' C' V' : Set (CoeffPair p)} {t' : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (E : SourceSection14Data hp hp1 A' C' V' t') (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p)
    (ha : a ∈ D.complex.originalWeightedComplexDomain w)
    (ha' : a ∈ E.complex.originalWeightedComplexDomain w) :
    originalWeightedBirkhoffMap hp hp1 s w a = originalWeightedBirkhoffMap hp hp1 t' w a := by
  simpa only [WeightedCoeffPair.exponentInclusion_refl] using
    D.weighted_complex_exponent E w le_rfl a ha (by simpa using ha')

end NLS.ZakharovShabat
