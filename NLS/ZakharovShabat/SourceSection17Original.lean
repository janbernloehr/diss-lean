import NLS.ZakharovShabat.SourceBirkhoffOriginalCanonicalImages
import NLS.ZakharovShabat.SourceBirkhoffOriginalFlowSign
import NLS.ZakharovShabat.SourceBirkhoffLemma17_5

/-!
# Section 17 for the original Birkhoff family

The original map is a local analytic diffeomorphism and globally injective
for every finite p>1, and onto for p≤2. The same family retains its exact
inverse derivatives, original Hilbert angle flow, and isospectral images.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original Sections 12–16 with global injectivity and the stated surjectivity range. -/
structure SourceSection17OriginalData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W₀ W V : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop extends
    SourceSection16OriginalData hp hp1 W₀ W V s where
  proposition17_2 : Function.Injective (sourceRealBirkhoffMap hp hp1 s)
  proposition17_3 : p ≤ 2 → Function.Surjective (sourceRealBirkhoffMap hp hp1 s)

namespace SourceSection17OriginalData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Proposition 17.1 includes both local inverse identities and the exact inverse derivative. -/
theorem proposition17_1 (D : SourceSection17OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) :
    ∃ g : (RealCoeff p × RealCoeff p) → realTypeSourceSubmodule p,
      AnalyticAt ℝ g (sourceRealBirkhoffMap hp hp1 s φ) ∧
      g (sourceRealBirkhoffMap hp hp1 s φ) = φ ∧
      (∀ᶠ ψ in 𝓝 φ, g (sourceRealBirkhoffMap hp hp1 s ψ) = ψ) ∧
      (∀ᶠ z in 𝓝 (sourceRealBirkhoffMap hp hp1 s φ), sourceRealBirkhoffMap hp hp1 s (g z) = z) ∧
      HasStrictFDerivAt g (D.complex.realJacobianEquivAll φ).symm.toContinuousLinearMap
        (sourceRealBirkhoffMap hp hp1 s φ) := D.complex.proposition17_1 φ

/-- The actual complex extension also has both local inverse identities at each real source. -/
theorem complex_localInverse (D : SourceSection17OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) :
    ∃ g : (Coeff p × Coeff p) → CoeffPair p,
      AnalyticAt ℂ g (sourceBirkhoffMap hp hp1 s φ.val) ∧
      g (sourceBirkhoffMap hp hp1 s φ.val) = φ.val ∧
      (∀ᶠ ψ in 𝓝 φ.val, g (sourceBirkhoffMap hp hp1 s ψ) = ψ) ∧
      (∀ᶠ z in 𝓝 (sourceBirkhoffMap hp hp1 s φ.val), sourceBirkhoffMap hp hp1 s (g z) = z) ∧
      HasStrictFDerivAt g (D.complex.jacobianEquivAll φ).symm.toContinuousLinearMap
        (sourceBirkhoffMap hp hp1 s φ.val) := D.complex.exists_complex_localInverse_all_exponents φ

/-- The global inverse is analytic everywhere on the target and differentiates to the
inverse of the actual Jacobian at the recovered source. -/
theorem global_inverse (D : SourceSection17OriginalData hp hp1 W₀ W V s) (hp2 : p ≤ 2) :
    ∃ e : realTypeSourceSubmodule p ≃ₜ (RealCoeff p × RealCoeff p),
      (∀ φ, e φ = sourceRealBirkhoffMap hp hp1 s φ) ∧
      AnalyticOnNhd ℝ (fun φ => e φ) univ ∧ AnalyticOnNhd ℝ (fun z => e.symm z) univ ∧
      ∀ z, HasStrictFDerivAt e.symm
        (D.complex.realJacobianEquivAll (e.symm z)).symm.toContinuousLinearMap z :=
  ⟨D.complex.realHomeomorph hp2,fun _ => rfl,D.complex.real_map_analytic,
    D.complex.realHomeomorph_symm_analytic hp2,D.complex.realHomeomorph_symm_hasStrictFDerivAt hp2⟩

/-- Lemma 17.5: compact target tori and all-exponent inclusion, with equality and
source compactness in the stated range 1<p≤2. -/
theorem lemma17_5 (D : SourceSection17OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) :
    IsCompact (RealCoeff.actionTorus p (fun n => (sourceRealAction hp hp1 φ.val φ.property n).re)) ∧
    sourceRealBirkhoffMap hp hp1 s '' sourceIsospectralSet hp φ ⊆
      RealCoeff.actionTorus p (fun n => (sourceRealAction hp hp1 φ.val φ.property n).re) ∧
    (p ≤ 2 → sourceRealBirkhoffMap hp hp1 s '' sourceIsospectralSet hp φ =
      RealCoeff.actionTorus p (fun n => (sourceRealAction hp hp1 φ.val φ.property n).re) ∧
        IsCompact (sourceIsospectralSet hp φ)) :=
  ⟨RealCoeff.isCompact_actionTorus hp _,D.complex.image_isospectralSet_subset_actionTorus φ,
    fun hp2 => D.complex.lemma17_5_i hp2 φ⟩

end SourceSection17OriginalData

/-- The original Section 17 package is constructed without any supplied inverse,
injectivity, flow, or isospectral-completeness hypothesis. -/
theorem sourceSection17_original (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourceSection17OriginalData hp hp1 W₀ W V s := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection16_original hp hp1
  exact ⟨W₀,W,V,s,D,D.complex.proposition17_2,D.complex.proposition17_3⟩

end NLS.ZakharovShabat
