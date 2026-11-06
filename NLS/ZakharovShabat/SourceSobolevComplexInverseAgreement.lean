import NLS.ZakharovShabat.SourceBirkhoffSobolevGlobalInverse

/-! # Complex inverse germs and the actual global Sobolev inverse

A complex left inverse agrees on a full real neighborhood with the global
native Sobolev inverse. Continuity of the latter pulls the left-inverse germ
back to the real target. No separate real-compatibility assumption is needed.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every actual complex left-inverse germ agrees with the original global
real Sobolev inverse on a complete real target neighborhood. -/
theorem complex_leftInverse_sobolev_agreement
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ))
    (g : WeightedCoeffPair (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ)) p →
      WeightedCoeffPair (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ)) p)
    (hl : ∀ᶠ b in 𝓝 a.val,
      g (originalWeightedBirkhoffMap hp hp1 s (sourceSobolevSpectralWeight σ hσ) b) = b) :
    ∀ᶠ z in 𝓝 (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a),
      g (WeightedCoeffPair.complexCLM (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ)) z) =
        ((D.originalWeightedRealSobolevEquiv hp2 σ hσ).symm z).val := by
  let w := sourceSobolevSpectralWeight σ hσ
  let e := D.originalWeightedRealSobolevEquiv hp2 σ hσ
  let z₀ := D.originalWeightedRealMap w a
  have hbase : (e.symm z₀).val = a.val := congrArg Subtype.val (e.symm_apply_apply a)
  have hc : ContinuousAt (fun z => (e.symm z).val) z₀ :=
    continuous_subtype_val.continuousAt.comp
      (D.originalWeightedRealSobolevEquiv_symm_analytic hp2 σ hσ z₀ (mem_univ _)).continuousAt
  have ht : Tendsto (fun z => (e.symm z).val) (𝓝 z₀) (𝓝 a.val) := by
    simpa only [hbase] using hc.tendsto
  filter_upwards [ht.eventually hl] with z hz
  have hi := D.originalWeightedRealMap_complex_inclusion w (e.symm z)
  have he : D.originalWeightedRealMap w (e.symm z) = z := e.apply_symm_apply z
  rw [he] at hi
  exact (congrArg g hi).trans hz

/-- An actual holomorphic inverse germ with exact real-neighborhood agreement
is constructed at every original Sobolev source in the global onto range. -/
theorem exists_complex_sobolevInverse_germ
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) :
    ∃ g : WeightedCoeffPair (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ)) p →
        WeightedCoeffPair (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ)) p,
      AnalyticAt ℂ g (WeightedCoeffPair.complexCLM (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ))
        (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a)) ∧
      g (WeightedCoeffPair.complexCLM (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ))
        (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a)) = a.val ∧
      ∀ᶠ z in 𝓝 (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a),
        g (WeightedCoeffPair.complexCLM (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ)) z) =
          ((D.originalWeightedRealSobolevEquiv hp2 σ hσ).symm z).val := by
  obtain ⟨g,hg,hbase,hl,_,_⟩ := D.exists_originalWeighted_complex_localInverse
    (sourceSobolevSpectralWeight σ hσ) a
  refine ⟨g,?_,?_,D.complex_leftInverse_sobolev_agreement hp2 σ hσ a g hl⟩
  · rw [D.originalWeightedRealMap_complex_inclusion]
    exact hg
  · rw [D.originalWeightedRealMap_complex_inclusion]
    exact hbase

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
