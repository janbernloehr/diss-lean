import NLS.ZakharovShabat.SourceBirkhoffJacobianCompact

/-! # Lemma 16.3: the normalized Jacobian is identity plus compact

The explicitly inverted free Fourier transform normalizes the genuine
Birkhoff Jacobian. Normalization preserves isomorphisms, varies analytically,
and turns the compact Fourier remainder into a compact perturbation of
identity at every real source, for every finite exponent strictly above one.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The operator Aφ = (d₀Ω)⁻¹ dφΩ, normalized by the exact free Fourier isomorphism. -/
def sourceBirkhoffNormalizedJacobian (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (φ : CoeffPair p) :
    CoeffPair p →L[ℂ] CoeffPair p :=
  sourceBirkhoffFourierInverse.comp (sourceBirkhoffJacobian hp hp1 s φ)

/-- Normalization carries the actual Fourier remainder to Aφ minus identity. -/
theorem sourceBirkhoffNormalizedJacobian_sub_id
    (hp : p ≠ ⊤) (hp1 : 1 < p) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (φ : CoeffPair p) :
    sourceBirkhoffNormalizedJacobian hp hp1 s φ-ContinuousLinearMap.id ℂ (CoeffPair p) =
      sourceBirkhoffFourierInverse.comp (sourceBirkhoffJacobianRemainder hp hp1 s φ) := by
  ext h
  simp [sourceBirkhoffNormalizedJacobian,sourceBirkhoffJacobianRemainder]

/-- Bijectivity of the actual derivative is equivalent to bijectivity of Aφ. -/
theorem sourceBirkhoffNormalizedJacobian_bijective_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (φ : CoeffPair p) :
    Function.Bijective (sourceBirkhoffNormalizedJacobian hp hp1 s φ) ↔
      Function.Bijective (sourceBirkhoffJacobian hp hp1 s φ) :=
  (sourceBirkhoffFourierEquiv (p := p)).symm.bijective.of_comp_iff' _

/-- The same equivalence holds for bounded linear isomorphisms, with explicit
transport by the free Fourier equivalence in either direction. -/
theorem sourceBirkhoffJacobian_isomorphism_iff_normalized
    (hp : p ≠ ⊤) (hp1 : 1 < p) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (φ : CoeffPair p) :
    (∃ e : CoeffPair p ≃L[ℂ] (Coeff p × Coeff p), e.toContinuousLinearMap = sourceBirkhoffJacobian hp hp1 s φ) ↔
    (∃ e : CoeffPair p ≃L[ℂ] CoeffPair p, e.toContinuousLinearMap = sourceBirkhoffNormalizedJacobian hp hp1 s φ) := by
  constructor
  · rintro ⟨e,he⟩
    refine ⟨e.trans sourceBirkhoffFourierEquiv.symm,?_⟩
    ext h : 1
    change sourceBirkhoffFourierInverse (e h) = sourceBirkhoffFourierInverse (sourceBirkhoffJacobian hp hp1 s φ h)
    exact congrArg sourceBirkhoffFourierInverse (congrArg (fun L => L h) he)
  · rintro ⟨e,he⟩
    refine ⟨e.trans sourceBirkhoffFourierEquiv,?_⟩
    ext h : 1
    change sourceBirkhoffFourier (e h) = sourceBirkhoffJacobian hp hp1 s φ h
    have hv := congrArg (fun L : CoeffPair p →L[ℂ] CoeffPair p => L h) he
    change e h = sourceBirkhoffNormalizedJacobian hp hp1 s φ h at hv
    rw [hv]
    exact sourceBirkhoffFourier_fourierInverse _

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The actual normalized Jacobian is complex analytic on the constructed domain. -/
theorem normalizedJacobian_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    AnalyticOnNhd ℂ (sourceBirkhoffNormalizedJacobian hp hp1 s) W := by
  let post := ContinuousLinearMap.compL ℂ (CoeffPair p) (Coeff p × Coeff p) (CoeffPair p)
    sourceBirkhoffFourierInverse
  exact post.comp_analyticOnNhd D.jacobian_analytic

/-- The normalized Jacobian varies real analytically on the whole real source space. -/
theorem normalizedJacobian_real_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    AnalyticOnNhd ℝ (fun φ : realTypeSourceSubmodule p => sourceBirkhoffNormalizedJacobian hp hp1 s φ.val) univ := by
  intro φ _
  have h := (D.normalizedJacobian_analytic φ.val (D.real_subset φ.property)).restrictScalars (𝕜 := ℝ)
  exact h.comp ((realTypeSourceSubmodule p).subtypeL.analyticAt (𝕜 := ℝ) (x := φ))

/-- At the free source the normalized Jacobian is exactly identity. -/
theorem normalizedJacobian_zero
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    sourceBirkhoffNormalizedJacobian hp hp1 s 0 = ContinuousLinearMap.id ℂ (CoeffPair p) := by
  ext h
  simp [sourceBirkhoffNormalizedJacobian,D.jacobian_zero]

/-- Lemma 16.3's compact perturbation at every real source, with no finite-gap hypothesis. -/
theorem isCompactOperator_normalizedJacobian_sub_id
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceSubmodule p) :
    IsCompactOperator (sourceBirkhoffNormalizedJacobian hp hp1 s φ.val-ContinuousLinearMap.id ℂ (CoeffPair p)) := by
  rw [sourceBirkhoffNormalizedJacobian_sub_id]
  exact (D.isCompactOperator_jacobianRemainder_real φ).clm_comp sourceBirkhoffFourierInverse

end SourceBirkhoffMapComplexData

/-- The complete Lemma 16.3 for a constructed Birkhoff family: real-analytic
normalized Jacobian, compact difference from identity at every real source,
and equivalence of the two bounded-isomorphism assertions. -/
theorem exists_sourceBirkhoffFamily_lemma16_3 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s ∧
      AnalyticOnNhd ℝ (fun φ : realTypeSourceSubmodule p => sourceBirkhoffNormalizedJacobian hp hp1 s φ.val) univ ∧
      ∀ φ : realTypeSourceSubmodule p,
        IsCompactOperator (sourceBirkhoffNormalizedJacobian hp hp1 s φ.val-ContinuousLinearMap.id ℂ (CoeffPair p)) ∧
        ((∃ e : CoeffPair p ≃L[ℂ] (Coeff p × Coeff p), e.toContinuousLinearMap = sourceBirkhoffJacobian hp hp1 s φ.val) ↔
         (∃ e : CoeffPair p ≃L[ℂ] CoeffPair p, e.toContinuousLinearMap = sourceBirkhoffNormalizedJacobian hp hp1 s φ.val)) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W₀,B,W,s,D,D.normalizedJacobian_real_analytic,fun φ =>
    ⟨D.isCompactOperator_normalizedJacobian_sub_id φ,sourceBirkhoffJacobian_isomorphism_iff_normalized hp hp1 s φ.val⟩⟩

end NLS.ZakharovShabat
