import NLS.ZakharovShabat.SourceBirkhoffWeightedRealLocalInverse
import NLS.ZakharovShabat.SourceBirkhoffSobolevRange

/-! # Global analytic Birkhoff inverses on the original Sobolev spaces

For 1<p<=2 and every nonnegative real Sobolev order, the existing native
weighted bijection has a continuous real analytic inverse. Local uniqueness
identifies it with the constructed analytic inverse germs and their derivatives.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual native Sobolev inverse is real analytic at every target. -/
theorem originalWeightedRealSobolevEquiv_symm_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    AnalyticOnNhd ℝ (D.originalWeightedRealSobolevEquiv hp2 t ht).symm univ := by
  intro z _
  let w := sourceSobolevSpectralWeight t ht
  let a := (D.originalWeightedRealSobolevEquiv hp2 t ht).symm z
  have ha : D.originalWeightedRealMap w a = z :=
    (D.originalWeightedRealSobolevEquiv hp2 t ht).apply_symm_apply z
  obtain ⟨g,hg,_,_,hr,_⟩ := D.exists_originalWeighted_real_localInverse w a
  rw [ha] at hg hr
  apply hg.congr
  filter_upwards [hr] with y hy
  apply D.originalWeightedRealMap_injective w
  exact hy.trans ((D.originalWeightedRealSobolevEquiv hp2 t ht).apply_symm_apply y).symm

/-- The global Sobolev inverse has the actual bounded inverse Jacobian as strict derivative. -/
theorem originalWeightedRealSobolevEquiv_symm_hasStrictFDerivAt
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t)
    (z : WithLp p (WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p ×
      WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p)) :
    HasStrictFDerivAt (D.originalWeightedRealSobolevEquiv hp2 t ht).symm
      (D.originalWeightedRealJacobianEquiv (sourceSobolevSpectralWeight t ht)
        ((D.originalWeightedRealSobolevEquiv hp2 t ht).symm z)).symm.toContinuousLinearMap z := by
  let w := sourceSobolevSpectralWeight t ht
  let a := (D.originalWeightedRealSobolevEquiv hp2 t ht).symm z
  have ha : D.originalWeightedRealMap w a = z :=
    (D.originalWeightedRealSobolevEquiv hp2 t ht).apply_symm_apply z
  obtain ⟨g,_,_,_,hr,hd⟩ := D.exists_originalWeighted_real_localInverse w a
  rw [ha] at hr hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hr] with y hy
  apply D.originalWeightedRealMap_injective w
  exact hy.trans ((D.originalWeightedRealSobolevEquiv hp2 t ht).apply_symm_apply y).symm

/-- The actual Sobolev Birkhoff map as a homeomorphism in its native weighted norms. -/
def originalWeightedRealSobolevHomeomorph
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight t ht) ≃ₜ
      WithLp p (WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p ×
        WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p) where
  toEquiv := D.originalWeightedRealSobolevEquiv hp2 t ht
  continuous_toFun := D.originalWeightedRealMap_continuous _
  continuous_invFun := continuous_iff_continuousAt.mpr
    (fun z => (D.originalWeightedRealSobolevEquiv_symm_analytic hp2 t ht z (mem_univ z)).continuousAt)

/-- The homeomorphism is exactly the original weighted real map. -/
@[simp] theorem originalWeightedRealSobolevHomeomorph_apply
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight t ht)) :
    D.originalWeightedRealSobolevHomeomorph hp2 t ht a =
      D.originalWeightedRealMap (sourceSobolevSpectralWeight t ht) a := rfl

/-- Its inverse is exactly the previously constructed native Sobolev inverse. -/
@[simp] theorem originalWeightedRealSobolevHomeomorph_symm_apply
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t)
    (z : WithLp p (WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p ×
      WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p)) :
    (D.originalWeightedRealSobolevHomeomorph hp2 t ht).symm z =
      (D.originalWeightedRealSobolevEquiv hp2 t ht).symm z := rfl

/-- The actual Sobolev homeomorphism is real analytic on its whole source. -/
theorem originalWeightedRealSobolevHomeomorph_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    AnalyticOnNhd ℝ (D.originalWeightedRealSobolevHomeomorph hp2 t ht) univ :=
  D.originalWeightedRealMap_analytic _

/-- Its inverse is real analytic on the whole native Sobolev target. -/
theorem originalWeightedRealSobolevHomeomorph_symm_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    AnalyticOnNhd ℝ (D.originalWeightedRealSobolevHomeomorph hp2 t ht).symm univ :=
  D.originalWeightedRealSobolevEquiv_symm_analytic hp2 t ht

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
