import NLS.ZakharovShabat.SourceBirkhoffRealJacobian

/-! # Analytic local inversion of the real Birkhoff map for `2 ≤ p < ∞`

This proves the upper-exponent part of Proposition 17.1. The inverse
acts on the actual real sequence space, is real analytic near the image,
and has derivative equal to the inverse of the actual real Jacobian.
The lower-exponent case is not asserted here.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- An analytic local inverse of the real Birkhoff map at every real
source in the range `2 ≤ p < ∞`, with both actual inverse identities. -/
theorem exists_real_localInverse
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p) :
    ∃ g : (RealCoeff p × RealCoeff p) → realTypeSourceSubmodule p,
      AnalyticAt ℝ g (sourceRealBirkhoffMap hp hp1 s φ) ∧
      g (sourceRealBirkhoffMap hp hp1 s φ) = φ ∧
      (∀ᶠ ψ in 𝓝 φ, g (sourceRealBirkhoffMap hp hp1 s ψ) = ψ) ∧
      (∀ᶠ z in 𝓝 (sourceRealBirkhoffMap hp hp1 s φ), sourceRealBirkhoffMap hp hp1 s (g z) = z) ∧
      HasStrictFDerivAt g (D.realJacobianEquiv h2p φ).symm.toContinuousLinearMap
        (sourceRealBirkhoffMap hp hp1 s φ) := by
  have ha := D.real_map_analytic φ (mem_univ φ)
  have hd : HasStrictFDerivAt (sourceRealBirkhoffMap hp hp1 s)
      (D.realJacobianEquiv h2p φ).toContinuousLinearMap φ :=
    ha.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  let e := hd.toOpenPartialHomeomorph (sourceRealBirkhoffMap hp hp1 s)
  have he : (e : realTypeSourceSubmodule p → (RealCoeff p × RealCoeff p)) = sourceRealBirkhoffMap hp hp1 s :=
    hd.toOpenPartialHomeomorph_coe
  have hg : AnalyticAt ℝ e.symm (sourceRealBirkhoffMap hp hp1 s φ) := by
    have h := e.analyticAt_symm' hd.mem_toOpenPartialHomeomorph_source
      (by rw [he]; exact ha) (i := D.realJacobianEquiv h2p φ) (by rw [he]; rfl)
    rw [he] at h
    exact h
  exact ⟨hd.localInverse _ _ _, hg, hd.localInverse_apply_image,
    hd.eventually_left_inverse, hd.eventually_right_inverse, hd.to_localInverse⟩


end SourceBirkhoffMapComplexData

/-- A constructed Birkhoff family supplies an analytic real local inverse
at every real source, without a supplied invertibility premise. -/
theorem exists_sourceBirkhoffFamily_localInverse_of_two_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s ∧
      ∀ φ : realTypeSourceSubmodule p,
        ∃ g : (RealCoeff p × RealCoeff p) → realTypeSourceSubmodule p,
          AnalyticAt ℝ g (sourceRealBirkhoffMap hp hp1 s φ) ∧
          g (sourceRealBirkhoffMap hp hp1 s φ) = φ ∧
          (∀ᶠ ψ in 𝓝 φ, g (sourceRealBirkhoffMap hp hp1 s ψ) = ψ) ∧
          (∀ᶠ z in 𝓝 (sourceRealBirkhoffMap hp hp1 s φ), sourceRealBirkhoffMap hp hp1 s (g z) = z) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  refine ⟨W₀,B,W,s,D,fun φ => ?_⟩
  obtain ⟨g,ha,hg,hl,hr,_⟩ := D.exists_real_localInverse h2p φ
  exact ⟨g,ha,hg,hl,hr⟩

end NLS.ZakharovShabat
