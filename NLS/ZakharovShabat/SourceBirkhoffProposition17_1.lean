import NLS.ZakharovShabat.SourceBirkhoffRealJacobian
import NLS.ZakharovShabat.SourceBirkhoffJacobianAllExponents

/-! # Proposition 17.1: the Birkhoff map is a local analytic diffeomorphism

For every `1 < p < ∞`, the actual real Birkhoff derivative is a bounded
linear isomorphism at every real source. The inverse function theorem
supplies real analytic local inverses with both local inverse identities
and the exact inverse derivative. The final theorem constructs the family.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Bijectivity of the actual real derivative for every `1 < p < ∞`. -/
theorem real_jacobian_bijective_all_exponents
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    Function.Bijective (fderiv ℝ (sourceRealBirkhoffMap hp hp1 s) φ) :=
  D.real_jacobian_bijective_of_complex φ (D.jacobian_bijective_all_exponents φ)

/-- The actual real Jacobian as a bounded equivalence, throughout the full range. -/
def realJacobianEquivAll
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    realTypeSourceSubmodule p ≃L[ℝ] (RealCoeff p × RealCoeff p) :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ (sourceRealBirkhoffMap hp hp1 s) φ)
    (LinearMap.ker_eq_bot.mpr (D.real_jacobian_bijective_all_exponents φ).1)
    (LinearMap.range_eq_top.mpr (D.real_jacobian_bijective_all_exponents φ).2)

@[simp] theorem realJacobianEquivAll_toContinuousLinearMap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    (D.realJacobianEquivAll φ).toContinuousLinearMap =
      fderiv ℝ (sourceRealBirkhoffMap hp hp1 s) φ := rfl

/-- An analytic local inverse of the real Birkhoff map at every real
source in the range `1 < p < ∞`, with both actual inverse identities. -/
theorem proposition17_1
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    ∃ g : (RealCoeff p × RealCoeff p) → realTypeSourceSubmodule p,
      AnalyticAt ℝ g (sourceRealBirkhoffMap hp hp1 s φ) ∧
      g (sourceRealBirkhoffMap hp hp1 s φ) = φ ∧
      (∀ᶠ ψ in 𝓝 φ, g (sourceRealBirkhoffMap hp hp1 s ψ) = ψ) ∧
      (∀ᶠ z in 𝓝 (sourceRealBirkhoffMap hp hp1 s φ), sourceRealBirkhoffMap hp hp1 s (g z) = z) ∧
      HasStrictFDerivAt g (D.realJacobianEquivAll φ).symm.toContinuousLinearMap
        (sourceRealBirkhoffMap hp hp1 s φ) := by
  have ha := D.real_map_analytic φ (mem_univ φ)
  have hd : HasStrictFDerivAt (sourceRealBirkhoffMap hp hp1 s)
      (D.realJacobianEquivAll φ).toContinuousLinearMap φ :=
    ha.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  let e := hd.toOpenPartialHomeomorph (sourceRealBirkhoffMap hp hp1 s)
  have he : (e : realTypeSourceSubmodule p → (RealCoeff p × RealCoeff p)) = sourceRealBirkhoffMap hp hp1 s :=
    hd.toOpenPartialHomeomorph_coe
  have hg : AnalyticAt ℝ e.symm (sourceRealBirkhoffMap hp hp1 s φ) := by
    have h := e.analyticAt_symm' hd.mem_toOpenPartialHomeomorph_source
      (by rw [he]; exact ha) (i := D.realJacobianEquivAll φ) (by rw [he]; rfl)
    rw [he] at h
    exact h
  exact ⟨hd.localInverse _ _ _, hg, hd.localInverse_apply_image,
    hd.eventually_left_inverse, hd.eventually_right_inverse, hd.to_localInverse⟩


end SourceBirkhoffMapComplexData

/-- A constructed Birkhoff family supplies an analytic real local inverse
at every real source, without a supplied invertibility premise. -/
theorem exists_sourceBirkhoffFamily_proposition17_1
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
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
  obtain ⟨g,ha,hg,hl,hr,_⟩ := D.proposition17_1 φ
  exact ⟨g,ha,hg,hl,hr⟩

end NLS.ZakharovShabat
