import NLS.ZakharovShabat.SourceQEquation
import NLS.ZakharovShabat.WeightedResonantReduction

/-!
# Lemma 6.6 for the original source pencil

The actual two-mode matrix detects the original periodic spectrum. Its kernel
reconstructs every original-domain eigenfunction with unchanged resonant
amplitudes. One local threshold works on all sufficiently distant closed strips.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Domain inclusion preserves the two actual resonant amplitudes. -/
theorem sourceWeightedDomainInput_resonantCoordinates (w : SpectralWeight) (n : ℤ)
    (f : WeightedDomain w.toWeight p) :
    resonantCoordinates (Weight.sobolev 1) n (sourceWeightedDomainInput w f) =
      resonantCoordinates w.toWeight.oneDerivative n f := by
  funext i
  fin_cases i <;> simp

/-- The source's two-dimensional map in the ordered physical resonant basis. -/
def sourceResonantMatrix (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  weightedResonantMatrix hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h

/-- Reconstruct an actual original-domain vector from its two resonant amplitudes. -/
def sourceResonantReconstruction (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    (Fin 2 → ℂ) →L[ℂ] WeightedCoeffPair (Weight.sobolev 1) p :=
  sourceUnitDomainEquiv.toContinuousLinearMap.comp
    (weightedReconstruction hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h)

/-- The reconstruction is the resonant domain lift plus the actual unique Q-solution. -/
theorem sourceResonantReconstruction_eq (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (c : Fin 2 → ℂ) :
    sourceResonantReconstruction hp φ n z hz h c =
      sourceUnitDomainEquiv (resonantSynthesis SpectralWeight.one.toWeight.oneDerivative n c) +
        sourceQSolution hp φ n z hz h
          (sourceUnitDomainEquiv (resonantSynthesis SpectralWeight.one.toWeight.oneDerivative n c)) := by
  rw [sourceQSolution_unitDomain]
  change sourceUnitDomainEquiv (_ + _) = _
  exact map_add _ _ _

/-- Reconstruction retains exactly the specified amplitudes. -/
@[simp] theorem sourceResonantReconstruction_coordinates (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (c : Fin 2 → ℂ) :
    resonantCoordinates (Weight.sobolev 1) n (sourceResonantReconstruction hp φ n z hz h c) = c := by
  change resonantCoordinates (Weight.sobolev 1) n
    (sourceUnitDomainEquiv (weightedReconstruction hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h c)) = c
  rw [sourceUnitDomainEquiv_apply, sourceWeightedDomainInput_resonantCoordinates,
    resonantCoordinates_reconstruction]

/-- Nonzero resonant amplitudes reconstruct nonzero original-domain vectors, and conversely. -/
theorem sourceResonantReconstruction_ne_zero_iff (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (c : Fin 2 → ℂ) : sourceResonantReconstruction hp φ n z hz h c ≠ 0 ↔ c ≠ 0 := by
  constructor
  · intro hc he; exact hc (by rw [he,map_zero])
  · intro hc he
    apply hc
    have he' := congrArg (resonantCoordinates (Weight.sobolev 1) n) he
    simpa only [sourceResonantReconstruction_coordinates, map_zero] using he'

/-- The full original differential residual equals the synthesized two-mode matrix residual. -/
theorem sourceResonantReconstruction_residual (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (c : Fin 2 → ℂ) :
    sourceSpectralPencil hp φ z (sourceResonantReconstruction hp φ n z hz h c) =
      sourceWeightedPeriodTwoInput SpectralWeight.one
        (resonantSynthesis SpectralWeight.one.toWeight n ((sourceResonantMatrix hp φ n z hz h).mulVec c)) := by
  change sourceSpectralPencil hp φ z
    (sourceUnitDomainEquiv (weightedReconstruction hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h c)) = _
  rw [sourceUnitDomainEquiv_apply]
  have he := sourceWeightedPencil_eq hp SpectralWeight.one (unitWeightedPairEquiv φ) z
    (weightedReconstruction hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h c)
  rw [sourceWeightedInput_unitWeightedPairEquiv, weightedReconstruction_residual] at he
  simpa only [sourceResonantMatrix, weightedResonantMatrix_mulVec] using he

/-- Exactly the matrix kernel reconstructs eigenvectors of the original pencil. -/
theorem sourceResonantReconstruction_kernel_iff (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (c : Fin 2 → ℂ) :
    sourceSpectralPencil hp φ z (sourceResonantReconstruction hp φ n z hz h c) = 0 ↔
      (sourceResonantMatrix hp φ n z hz h).mulVec c = 0 := by
  rw [sourceResonantReconstruction_residual, ← map_zero (sourceWeightedPeriodTwoInput (p := p) SpectralWeight.one),
    (sourceWeightedPeriodTwoInput_injective SpectralWeight.one).eq_iff,
    ← map_zero (resonantSynthesis (p := p) SpectralWeight.one.toWeight n),
    (resonantSynthesis_injective SpectralWeight.one.toWeight n).eq_iff]

/-- Every original-domain eigenvector is recovered from its own resonant amplitudes. -/
theorem sourceResonantReconstruction_of_eigenvector (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (f : WeightedCoeffPair (Weight.sobolev 1) p) (hf : sourceSpectralPencil hp φ z f = 0) :
    sourceResonantReconstruction hp φ n z hz h (resonantCoordinates (Weight.sobolev 1) n f) = f := by
  obtain ⟨f,rfl⟩ := (sourceUnitDomainEquiv (p := p)).surjective f
  have he : weightedFreePencil SpectralWeight.one.toWeight z f =
      weightedDomainPotential hp SpectralWeight.one (unitWeightedPairEquiv φ) f :=
    (sourceWeightedPencil_zero_iff hp SpectralWeight.one (unitWeightedPairEquiv φ) z f).mp
      (by simpa only [sourceUnitDomainEquiv_apply, sourceWeightedInput_unitWeightedPairEquiv] using hf)
  change sourceUnitDomainEquiv (weightedReconstruction hp SpectralWeight.one
    (unitWeightedPairEquiv φ) n z hz h _) = _
  simp only [sourceUnitDomainEquiv_apply, sourceWeightedDomainInput_resonantCoordinates]
  rw [weightedReconstruction_of_eigenvector hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h f he]

/-- Lemma 6.6: the determinant detects the actual original periodic spectrum. -/
theorem sourceLemma6_6 (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    z ∉ sourceResolventSet hp φ ↔ (sourceResonantMatrix hp φ n z hz h).det = 0 :=
  (sourcePeriodTwoSpectrum_iff hp φ z).trans
    ((unit_weighted_eigenvector_iff_periodicSpectrum hp (unitWeightedPairEquiv φ) z).symm.trans
      (weighted_eigenvector_iff_resonant_det_zero hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h))

/-- The determinant is also equivalent to a nonzero eigenvector in the full original derivative domain. -/
theorem sourceLemma6_6_eigenvector (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1) :
    (∃ f : WeightedCoeffPair (Weight.sobolev 1) p, f ≠ 0 ∧ sourceSpectralPencil hp φ z f = 0) ↔
      (sourceResonantMatrix hp φ n z hz h).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨f,hf0,hf⟩
    let c := resonantCoordinates (Weight.sobolev 1) n f
    have hr := sourceResonantReconstruction_of_eigenvector hp φ n z hz h f hf
    refine ⟨c,?_,?_⟩
    · intro hc; apply hf0; rw [← hr]; change sourceResonantReconstruction hp φ n z hz h c = 0
      rw [hc,map_zero]
    · apply (sourceResonantReconstruction_kernel_iff hp φ n z hz h c).mp
      rwa [hr]
  · rintro ⟨c,hc,hk⟩
    exact ⟨sourceResonantReconstruction hp φ n z hz h c,
      (sourceResonantReconstruction_ne_zero_iff hp φ n z hz h c).mpr hc,
      (sourceResonantReconstruction_kernel_iff hp φ n z hz h c).mpr hk⟩

private theorem sourceUniformPullback
    (e : CoeffPair p ≃ₗᵢ[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight p)
    (φ : CoeffPair p) (P : ℕ → WeightedCoeffPair SpectralWeight.one.toWeight p → Prop)
    (h : ∃ N : ℕ, 1 ≤ N ∧ ∃ V : Set (WeightedCoeffPair SpectralWeight.one.toWeight p),
      IsOpen V ∧ Convex ℝ V ∧ e φ ∈ V ∧ 0 ∈ V ∧ ∀ ψ ∈ V, P N ψ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, P N (e ψ) := by
  obtain ⟨N,hN,V,ho,hc,hφ,h0,hP⟩ := h
  exact ⟨N,hN,e ⁻¹' V,ho.preimage e.continuous,
    hc.linear_preimage (e.toLinearEquiv.toLinearMap.restrictScalars ℝ),hφ,
    by simpa only [Set.mem_preimage,map_zero] using h0,fun ψ hψ => hP (e ψ) hψ⟩

private theorem sourceUniformSmall (hp : p ≠ ⊤)
    (φ : WeightedCoeffPair SpectralWeight.one.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair SpectralWeight.one.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift hp SpectralWeight.one ψ n z hz‖ < 1 := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,_,hs⟩ := exists_uniform_complementarySquare_half hp SpectralWeight.one φ
  exact ⟨N,hN,U,ho,hc,hφ,h0,fun ψ hψ n hn z hz =>
    ((hs ψ hψ n hn z hz).1).trans_lt (by norm_num : (1:ℝ)/2 < 1)⟩

/-- The unchanged source criterion holds locally uniformly throughout the distant closed strips. -/
theorem sourceLemma6_6_uniform (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ∃ h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv ψ) n z hz‖ < 1,
          z ∉ sourceResolventSet hp ψ ↔ (sourceResonantMatrix hp ψ n z hz h).det = 0 := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hs⟩ := sourceUniformPullback unitWeightedPairEquiv φ _
    (sourceUniformSmall hp (unitWeightedPairEquiv φ))
  exact ⟨N,hN,U,ho,hc,hφ,h0,fun ψ hψ n hn z hz =>
    ⟨hs ψ hψ n hn z hz,sourceLemma6_6 hp ψ n z hz (hs ψ hψ n hn z hz)⟩⟩

end NLS.ZakharovShabat
