import NLS.ZakharovShabat.SourceBirkhoffNormalizedCutoff
import NLS.ZakharovShabat.SourceBirkhoffSection16Corrections

/-!
# Section 16 for the original Birkhoff family

The package retains all original-domain estimates and exponent compatibility.
Its actual Jacobian is analytic, equals the free Fourier operator at zero,
and normalizes to identity plus compact at every real source.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The original Section 15 family with its actual operator-valued derivative. -/
structure SourceSection16OriginalData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W₀ W V : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop extends
    SourceSection15OriginalData hp hp1 W₀ W V s where
  jacobian_analytic : AnalyticOnNhd ℂ (sourceBirkhoffJacobian hp hp1 s) V
  jacobian_zero : sourceBirkhoffJacobian hp hp1 s 0 = sourceBirkhoffFourier
  normalized_analytic : AnalyticOnNhd ℂ (sourceBirkhoffNormalizedJacobian hp hp1 s) V
  normalized_compact : ∀ φ : realTypeSourceSubmodule p,
    IsCompactOperator (sourceBirkhoffNormalizedJacobian hp hp1 s φ.val-
      ContinuousLinearMap.id ℂ (CoeffPair p))

namespace SourceSection16OriginalData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Actual coordinate gradients in the physical Holder-conjugate space represent
the full Jacobian at every complex point of its domain. -/
theorem jacobian_gradients [q.HolderConjugate p]
    (D : SourceSection16OriginalData hp hp1 W₀ W V s) (hq : q ≠ ⊤)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (h : CoeffPair p) (n : ℤ) :
    let X := CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (fun χ => (sourceBirkhoffMap hp hp1 s χ).1 n) ψ)
    let Y := CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (fun χ => (sourceBirkhoffMap hp hp1 s χ).2 n) ψ)
    (sourceBirkhoffJacobian hp hp1 s ψ h).1 n =
      Coeff.dualPairing (Coeff.reflection X.fst) h.fst+
      Coeff.dualPairing (Coeff.reflection X.snd) h.snd ∧
    (sourceBirkhoffJacobian hp hp1 s ψ h).2 n =
      Coeff.dualPairing (Coeff.reflection Y.fst) h.fst+
      Coeff.dualPairing (Coeff.reflection Y.snd) h.snd := by
  dsimp only
  rw [CoeffPair.dualPairing_conjugateGradient,CoeffPair.dualPairing_conjugateGradient,
    (D.complex.fderiv_coordinates n ψ hψ).1,(D.complex.fderiv_coordinates n ψ hψ).2]
  exact D.complex.jacobian_coordinates ψ hψ h n

/-- Lemma 16.3 for this same original family, at every real source. -/
theorem lemma16_3 (D : SourceSection16OriginalData hp hp1 W₀ W V s) :
    AnalyticOnNhd ℝ (fun φ : realTypeSourceSubmodule p =>
      sourceBirkhoffNormalizedJacobian hp hp1 s φ.val) univ ∧
    ∀ φ : realTypeSourceSubmodule p,
      IsCompactOperator (sourceBirkhoffNormalizedJacobian hp hp1 s φ.val-
        ContinuousLinearMap.id ℂ (CoeffPair p)) ∧
      ((∃ e : CoeffPair p ≃L[ℂ] (Coeff p × Coeff p),
        e.toContinuousLinearMap = sourceBirkhoffJacobian hp hp1 s φ.val) ↔
       (∃ e : CoeffPair p ≃L[ℂ] CoeffPair p,
        e.toContinuousLinearMap = sourceBirkhoffNormalizedJacobian hp hp1 s φ.val)) :=
  ⟨D.complex.normalizedJacobian_real_analytic,fun φ =>
    ⟨D.normalized_compact φ,sourceBirkhoffJacobian_isomorphism_iff_normalized hp hp1 s φ.val⟩⟩

end SourceSection16OriginalData

/-- Construct the Section 16 package for every finite exponent strictly above one. -/
theorem sourceSection16_original (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourceSection16OriginalData hp hp1 W₀ W V s := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection15_original hp hp1
  exact ⟨W₀,W,V,s,D,D.complex.jacobian_analytic,D.complex.jacobian_zero,
    D.complex.normalizedJacobian_analytic,D.complex.isCompactOperator_normalizedJacobian_sub_id⟩

end NLS.ZakharovShabat
