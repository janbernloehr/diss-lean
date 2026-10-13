import NLS.ZakharovShabat.SourceAuxiliarySpaces
import NLS.ZakharovShabat.SourceBoundarySeries

/-!
# Auxiliary mode series in the original weighted spaces

The amplitude representation gives norm-convergent series for finite
exponents and actual periodic distributional series for every Banach
exponent, including infinity. The physical waves carry the auxiliary phase.
The repeated D* summand printed on page 34 is formally refuted; the correct
D* and N* complement is proved in `SourceAuxiliarySpaces`.
-/

noncomputable section
open scoped ENNReal SchwartzMap FourierTransform
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The printed unnormalized boundary mode in the original weighted space. -/
def sourceWeightedAuxiliaryMode (b : BoundaryCondition) (s : ℝ) (n : ℤ) :
    sourceWeightedAuxiliarySubspace (p := p) b s :=
  sourceWeightedAuxiliaryAmplitudeEquiv b s (sourceWeightedSingle s n)

/-- The printed auxiliary-mode expansion converges in the original norm for finite p. -/
theorem hasSum_sourceWeightedAuxiliaryModes (hp : p ≠ ⊤) (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    HasSum (fun n : ℤ => a.val n • sourceWeightedAuxiliaryMode b s n)
      (sourceWeightedAuxiliaryAmplitudeEquiv b s a) := by
  let L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] sourceWeightedAuxiliarySubspace (p := p) b s :=
    (sourceWeightedAuxiliaryAmplitudeEquiv b s).toContinuousLinearMap
  have h := L.hasSum (hasSum_sourceWeightedSingle hp s a)
  convert h using 1
  · funext n
    exact (L.map_smul (a.val n) (sourceWeightedSingle s n)).symm
  · rfl

/-- The actual pair of periodic distributions represented by the boundary amplitudes. -/
def sourceAuxiliaryDistribution (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  (sobolevDistributionSynthesisCLM s (b.extensionSign • WeightedCoeff.reflection s a),
    sobolevDistributionSynthesisCLM s (Complex.I • a))

/-- The signed pair of actual wave distributions in the printed auxiliary basis. -/
def sourceAuxiliaryDistributionMode (b : BoundaryCondition) (n : ℤ) : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  (b.extensionSign • sourceWaveDistribution (-n), Complex.I • sourceWaveDistribution n)

/-- The auxiliary-mode series converges as distributions, including at infinity. -/
theorem hasSum_sourceAuxiliaryDistribution (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    HasSum (fun n : ℤ => a.val n • sourceAuxiliaryDistributionMode b n)
      (sourceAuxiliaryDistribution b s a) := by
  have h₁ := (Equiv.neg ℤ).hasSum_iff.mpr
    (hasSum_sourceWaveDistribution s (b.extensionSign • WeightedCoeff.reflection s a))
  have h₂ := hasSum_sourceWaveDistribution s (Complex.I • a)
  convert HasSum.prodMk h₁ h₂ using 1
  · funext n
    simp [sourceAuxiliaryDistributionMode, WeightedCoeff.smul_val, WeightedCoeff.reflection_apply,
      smul_smul, mul_comm]
  · rfl

/-- The series sum is the actual synthesis of the original finite-exponent coefficient pair. -/
theorem sourceAuxiliaryDistribution_eq_sourcePair (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    ((sobolevDistributionSynthesisCLM s).prodMap (sobolevDistributionSynthesisCLM s))
      (WeightedCoeffPair.toMax (Weight.sobolev s) p
        (sourceWeightedAuxiliaryAmplitudeEquiv b s a).val) = sourceAuxiliaryDistribution b s a := by
  rw [sourceWeightedAuxiliaryAmplitudeEquiv_apply]
  rfl

/-- The infinity series sum synthesizes the original signed coupled-supremum coefficients. -/
theorem sourceAuxiliaryDistribution_eq_sourcePairInfty (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) ⊤) :
    pairDistributionInftyCLM s (sourceWeightedAuxiliaryAmplitudeEquivInfty b s a).val =
      sourceAuxiliaryDistribution b s a := by
  rw [sourceWeightedAuxiliaryAmplitudeEquivInfty_apply]
  change (sobolevDistributionSynthesisCLM s (WeightedCoeff.reflection s (b.extensionSign • a)),
    sobolevDistributionSynthesisCLM s (Complex.I • a)) = _
  rw [map_smul]
  rfl

/-- The coefficient-space and distributional auxiliary modes agree. -/
theorem sourceAuxiliaryDistribution_single (b : BoundaryCondition) (s : ℝ) (n : ℤ) :
    sourceAuxiliaryDistribution b s (sourceWeightedSingle (p := p) s n) =
      sourceAuxiliaryDistributionMode b n := by
  simp only [sourceAuxiliaryDistribution, sourceWeightedSingle_reflection, map_smul,
    sourceWeightedSingle_distribution, sourceAuxiliaryDistributionMode]

/-- The modes act by the ordinary integrals of the printed physical waves. -/
theorem sourceAuxiliaryDistributionMode_physical (b : BoundaryCondition) (n : ℤ) (g : 𝓢(ℝ, ℂ)) :
    ((sourceAuxiliaryDistributionMode b n).1 g, (sourceAuxiliaryDistributionMode b n).2 g) =
      (b.extensionSign * ∫ x : ℝ, wave (-n) x * g x, Complex.I * ∫ x : ℝ, wave n x * g x) := by
  change (b.extensionSign * distributionSynthesis (lp.single 2 (-n) 1) g,
    Complex.I * distributionSynthesis (lp.single 2 n 1) g) = _
  rw [distributionSynthesis_single, distributionSynthesis_single]
  simp only [one_mul]

omit [Fact (1 ≤ p)] in
/-- A raw weighted zero mode is nonzero at every Sobolev order and exponent. -/
theorem sourceWeightedSingle_zero_ne_zero (s : ℝ) : sourceWeightedSingle (p := p) s 0 ≠ 0 := by
  intro h
  have he := congrArg (fun a : WeightedCoeff (Weight.sobolev s) p => a.val 0) h
  simp [sourceWeightedSingle_apply] at he

/-- The repeated D* summand on printed page 34 cannot be a direct complement of itself. -/
theorem not_isCompl_sourceWeightedAuxiliaryDirichlet_self (s : ℝ) :
    ¬ IsCompl (sourceWeightedAuxiliarySubspace (p := p) .dirichlet s)
      (sourceWeightedAuxiliarySubspace (p := p) .dirichlet s) := by
  intro h
  let e := sourceWeightedAuxiliaryAmplitudeEquiv (p := p) .dirichlet s
  let a := sourceWeightedSingle (p := p) s 0
  have hz := (Submodule.disjoint_def.mp h.disjoint) _ (e a).property (e a).property
  have hy : e a = 0 := Subtype.ext hz
  exact sourceWeightedSingle_zero_ne_zero (p := p) s (e.injective (hy.trans (map_zero e).symm))

/-- The same printed repeated-summand failure holds with the original infinity norm. -/
theorem not_isCompl_sourceWeightedAuxiliaryDirichletInfty_self (s : ℝ) :
    ¬ IsCompl (sourceWeightedAuxiliarySubspaceInfty .dirichlet s)
      (sourceWeightedAuxiliarySubspaceInfty .dirichlet s) := by
  intro h
  let e := sourceWeightedAuxiliaryAmplitudeEquivInfty .dirichlet s
  let a := sourceWeightedSingle (p := ⊤) s 0
  have hz := (Submodule.disjoint_def.mp h.disjoint) _ (e a).property (e a).property
  have hy : e a = 0 := Subtype.ext hz
  exact sourceWeightedSingle_zero_ne_zero (p := ⊤) s (e.injective (hy.trans (map_zero e).symm))

/-- Every finite-exponent auxiliary vector has exactly one norm-convergent mode expansion. -/
theorem existsUnique_sourceWeightedAuxiliaryExpansion (hp : p ≠ ⊤) (b : BoundaryCondition) (s : ℝ)
    (u : sourceWeightedAuxiliarySubspace (p := p) b s) :
    ∃! a : WeightedCoeff (Weight.sobolev s) p,
      HasSum (fun n : ℤ => a.val n • sourceWeightedAuxiliaryMode b s n) u := by
  let e := sourceWeightedAuxiliaryAmplitudeEquiv (p := p) b s
  refine ⟨e.symm u, ?_, ?_⟩
  · simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using hasSum_sourceWeightedAuxiliaryModes hp b s (e.symm u)
  · intro a ha
    apply e.injective
    rw [e.apply_symm_apply]
    exact (hasSum_sourceWeightedAuxiliaryModes hp b s a).unique ha

/-- Every infinity-norm auxiliary vector has a unique amplitude representation and actual distributional sum. -/
theorem existsUnique_sourceWeightedAuxiliaryInftyExpansion (b : BoundaryCondition) (s : ℝ)
    (u : sourceWeightedAuxiliarySubspaceInfty b s) :
    ∃! a : WeightedCoeff (Weight.sobolev s) ⊤,
      sourceWeightedAuxiliaryAmplitudeEquivInfty b s a = u ∧
      HasSum (fun n : ℤ => a.val n • sourceAuxiliaryDistributionMode b n)
        (pairDistributionInftyCLM s u.val) := by
  let e := sourceWeightedAuxiliaryAmplitudeEquivInfty b s
  refine ⟨e.symm u, ⟨e.apply_symm_apply u, ?_⟩, ?_⟩
  · have h := hasSum_sourceAuxiliaryDistribution b s (e.symm u)
    rw [← sourceAuxiliaryDistribution_eq_sourcePairInfty] at h
    simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using h
  · intro a ha
    exact e.injective (ha.1.trans (e.apply_symm_apply u).symm)

end NLS.ZakharovShabat
