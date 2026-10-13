import NLS.ZakharovShabat.SourceLemma6_4
import NLS.ZakharovShabat.SourcePeriodTwoDisplacement

/-!
# Lemma 6.5 and simultaneous contraction in the original source spaces

The shifted operator norm is characterized by its action on all inputs.
Unit weighting transports the unweighted operator isometrically to the original
component-sum norm. The tail retains |k|≥|n|, including its boundary.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The norm of the conjugated square is exactly the induced shifted operator norm. -/
theorem sourceSquareNorm_le_iff (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    {C : ℝ} (hC : 0 ≤ C) :
    ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ C ↔
      ∀ f, w.shiftedPairNorm n (weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz f)) ≤ C * w.shiftedPairNorm n f := by
  constructor
  · intro h f
    have hb := (weightedPotentialSquareInShift hp w φ n z hz).le_opNorm (w.pairModulation n f)
    simp only [weightedPotentialSquareInShift, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  · intro h
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro f
    simpa only [weightedPotentialSquareInShift, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, SpectralWeight.shiftedPairNorm, ContinuousLinearEquiv.apply_symm_apply]
      using h ((w.pairModulation n).symm f)

/-- The printed Lemma 6.5, including p=1, the exact tail cutoff, and its weight divisor. -/
theorem sourceLemma6_5 (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ weightedDoubleConstant (p := p) hp * ‖φ‖ *
      (‖φ‖ / (1 + |(n : ℝ)|) ^ (1 / p.toReal) +
        ‖weightedPairFourierTail w.toWeight n.natAbs φ‖ / w n) :=
  norm_weightedPotentialSquareInShift_le_source hp w φ n z hz

/-- At unit weight the shifted and ordinary squared operator norms agree exactly. -/
theorem sourceSquareNorm_one (hp : p ≠ ⊤)
    (φ : WeightedCoeffPair SpectralWeight.one.toWeight p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift hp SpectralWeight.one φ n z hz‖ =
      ‖(weightedPotentialInverse hp SpectralWeight.one φ n z hz).comp
        (weightedPotentialInverse hp SpectralWeight.one φ n z hz)‖ := by
  apply le_antisymm
  · apply (sourceSquareNorm_le_iff hp SpectralWeight.one φ n z hz (norm_nonneg _)).mpr
    intro f
    simp only [SpectralWeight.shiftedPairNorm_one hp]
    exact ((weightedPotentialInverse hp SpectralWeight.one φ n z hz).comp
      (weightedPotentialInverse hp SpectralWeight.one φ n z hz)).le_opNorm f
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    simpa only [ContinuousLinearMap.comp_apply, SpectralWeight.shiftedPairNorm_one hp] using
      (sourceSquareNorm_le_iff hp SpectralWeight.one φ n z hz (norm_nonneg _)).mp le_rfl f

/-- Forgetting a weight into the original pair agrees with the coefficient-preserving unit isometry. -/
theorem unitWeightedPairEquiv_sourceWeightedInput (w : SpectralWeight)
    (f : WeightedCoeffPair w.toWeight p) :
    unitWeightedPairEquiv (sourceWeightedPeriodTwoInput w f) = w.forgetPairWeight f := by
  apply weightedPair_ext <;> intro k <;> simp

/-- Unit weighting followed by the original-source inclusion is the identity. -/
@[simp] theorem sourceWeightedInput_unitWeightedPairEquiv (f : CoeffPair p) :
    sourceWeightedPeriodTwoInput SpectralWeight.one (unitWeightedPairEquiv f) = f := by
  apply (CoeffPair.toMax p).injective
  rw [toMax_sourceWeightedPeriodTwoInput, weightedBaseToPair_unitWeightedPairEquiv]

/-- The actual unweighted complementary potential operator on the original source pair. -/
def sourcePotentialInverse (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) : CoeffPair p →L[ℂ] CoeffPair p :=
  unitWeightedPairEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((weightedPotentialInverse hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz).comp
      unitWeightedPairEquiv.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The weighted operator and the actual original source operator agree on every weighted input. -/
theorem sourcePotentialInverse_weightedInput (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    sourcePotentialInverse hp (sourceWeightedPeriodTwoInput w φ) n z hz
      (sourceWeightedPeriodTwoInput w f) =
        sourceWeightedPeriodTwoInput w (weightedPotentialInverse hp w φ n z hz f) := by
  apply unitWeightedPairEquiv.injective
  simp only [sourcePotentialInverse, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply, unitWeightedPairEquiv_sourceWeightedInput,
    forgetPairWeight_potentialInverse]

/-- On arbitrary original inputs this is precisely Φ A_λ⁻¹ Q_n. -/
theorem sourcePotentialInverse_operator (hp : p ≠ ⊤) (φ f : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    sourcePotentialInverse hp φ n z hz f =
      sourceOperator hp φ
        (sourceWeightedDomainInput SpectralWeight.one
          (complementaryFreeDomainInverse SpectralWeight.one.toWeight n z hz (unitWeightedPairEquiv f))) -
      sourceOperator hp 0
        (sourceWeightedDomainInput SpectralWeight.one
          (complementaryFreeDomainInverse SpectralWeight.one.toWeight n z hz (unitWeightedPairEquiv f))) := by
  have he := sourcePotentialInverse_weightedInput hp SpectralWeight.one
    (unitWeightedPairEquiv φ) (unitWeightedPairEquiv f) n z hz
  rw [sourceLemma6_4_operator] at he
  simpa only [sourceWeightedInput_unitWeightedPairEquiv] using he

private theorem norm_isometry_transport {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F) (A : F →L[ℂ] F) :
    ‖e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (A.comp e.toContinuousLinearEquiv.toContinuousLinearMap)‖ = ‖A‖ := by
  let B := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (A.comp e.toContinuousLinearEquiv.toContinuousLinearMap)
  have hb (x : E) : ‖B x‖ = ‖A (e x)‖ := e.symm.norm_map _
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖B x‖ ≤ _
    rw [hb]
    simpa only [e.norm_map] using A.le_opNorm (e x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    have h := B.le_opNorm (e.symm y)
    simpa only [hb, e.apply_symm_apply, e.symm.norm_map] using h

/-- Transporting the square to the original component-sum norm introduces no constant. -/
theorem sourcePotentialInverse_square_norm (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖(sourcePotentialInverse hp φ n z hz).comp (sourcePotentialInverse hp φ n z hz)‖ =
      ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ := by
  rw [sourceSquareNorm_one]
  let e := unitWeightedPairEquiv (p := p)
  let T := weightedPotentialInverse hp SpectralWeight.one (e φ) n z hz
  calc
    _ = ‖e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((T.comp T).comp e.toContinuousLinearEquiv.toContinuousLinearMap)‖ := by
      congr 1
      ext f : 1
      simp only [sourcePotentialInverse, e, T, ContinuousLinearMap.comp_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.apply_symm_apply]
    _ = _ := norm_isometry_transport e (T.comp T)

/-- One neighborhood and cutoff give both printed half-contractions in the original norms. -/
theorem sourceLemma6_5_uniform_half (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ‖ψ‖ < ‖φ‖ + 1) ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift hp w ψ n z hz‖ ≤ 1 / 2 ∧
        ‖(sourcePotentialInverse hp (sourceWeightedPeriodTwoInput w ψ) n z hz).comp
          (sourcePotentialInverse hp (sourceWeightedPeriodTwoInput w ψ) n z hz)‖ ≤ 1 / 2 := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hnorm,hsmall⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,hnorm,?_⟩
  intro ψ hψ n hn z hz
  rw [sourcePotentialInverse_square_norm,unitWeightedPairEquiv_sourceWeightedInput,sourceSquareNorm_one]
  exact hsmall ψ hψ n hn z hz

end NLS.ZakharovShabat
