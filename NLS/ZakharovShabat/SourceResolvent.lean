import NLS.SequenceSpaces.PairNorm
import NLS.ZakharovShabat.ResolventAnalytic
import NLS.ZakharovShabat.PeriodicSpectrum
import NLS.ZakharovShabat.SourceFreeResolvent
import NLS.ZakharovShabat.ResolventCalculus

/-! # The complete resolvent in the original period-two source norms

The base and one-derivative domain both retain their finite component-sum
norms. Coefficient-preserving equivalences transport the actual spectral
pencil, full resolvent set, and inverse maps with both identities.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complete base-space resolvent in the original finite source norm. -/
def sourceResolvent (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.conjContinuousAlgEquiv (resolvent hp (CoeffPair.toMax p φ) z)

/-- The original spectral pencil on the source one-derivative domain. -/
def sourceSpectralPencil (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) :
    WeightedCoeffPair (Weight.sobolev 1) p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    ((spectralPencil hp (CoeffPair.toMax p φ) z).comp
      (WeightedCoeffPair.toMax (Weight.sobolev 1) p).toContinuousLinearMap)

/-- The inverse with values in the original one-derivative source norm. -/
def sourceResolventToDomain (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) :
    CoeffPair p →L[ℂ] WeightedCoeffPair (Weight.sobolev 1) p :=
  (WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm.toContinuousLinearMap.comp
    ((resolventToDomain hp (CoeffPair.toMax p φ) z).comp (CoeffPair.toMax p).toContinuousLinearMap)

/-- The complete resolvent set in the original source domain and base norms. -/
def sourceResolventSet (hp : p ≠ ⊤) (φ : CoeffPair p) : Set ℂ :=
  {z | Function.Bijective (sourceSpectralPencil hp φ z)}

/-- Changing equivalent norms preserves every spectral parameter, in both directions. -/
theorem sourceResolventSet_eq (hp : p ≠ ⊤) (φ : CoeffPair p) :
    sourceResolventSet hp φ = resolventSet hp (CoeffPair.toMax p φ) := by
  ext z
  change Function.Bijective ((CoeffPair.toMax p).symm ∘
    spectralPencil hp (CoeffPair.toMax p φ) z ∘ WeightedCoeffPair.toMax (Weight.sobolev 1) p) ↔ _
  rw [Function.Bijective.of_comp_iff' (CoeffPair.toMax p).symm.bijective,
    Function.Bijective.of_comp_iff _ (WeightedCoeffPair.toMax (Weight.sobolev 1) p).bijective]
  rfl

theorem isCompactOperator_sourceResolvent (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) : IsCompactOperator (sourceResolvent hp φ z) := by
  change IsCompactOperator ((CoeffPair.toMax p).symm.toContinuousLinearMap ∘
    resolvent hp (CoeffPair.toMax p φ) z ∘ (CoeffPair.toMax p).toContinuousLinearMap)
  exact ((isCompactOperator_resolvent hp _ z).comp_clm (CoeffPair.toMax p).toContinuousLinearMap).clm_comp
    (CoeffPair.toMax p).symm.toContinuousLinearMap

theorem analyticOnNhd_sourceResolvent (hp : p ≠ ⊤) (φ : CoeffPair p) : AnalyticOnNhd ℂ (sourceResolvent hp φ) (sourceResolventSet hp φ) := by
  intro z hz
  exact ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv.toContinuousLinearEquiv.analyticAt _).comp
    ((analyticOnNhd_resolvent hp _) z (by rwa [sourceResolventSet_eq] at hz))

theorem sourceSpectralPencil_sourceResolventToDomain (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceResolventSet hp φ) (a : CoeffPair p) :
    sourceSpectralPencil hp φ z (sourceResolventToDomain hp φ z a) = a := by
  change (CoeffPair.toMax p).symm (spectralPencil hp (CoeffPair.toMax p φ) z
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) p)
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm
        (resolventToDomain hp (CoeffPair.toMax p φ) z (CoeffPair.toMax p a))))) = a
  rw [ContinuousLinearEquiv.apply_symm_apply,
    spectralPencil_resolventToDomain hp _ z (by rwa [sourceResolventSet_eq] at hz), ContinuousLinearEquiv.symm_apply_apply]

theorem sourceResolventToDomain_sourceSpectralPencil (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceResolventSet hp φ)
    (a : WeightedCoeffPair (Weight.sobolev 1) p) : sourceResolventToDomain hp φ z (sourceSpectralPencil hp φ z a) = a := by
  change (WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm
    (resolventToDomain hp (CoeffPair.toMax p φ) z
      ((CoeffPair.toMax p) ((CoeffPair.toMax p).symm
        (spectralPencil hp (CoeffPair.toMax p φ) z (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))))) = a
  rw [ContinuousLinearEquiv.apply_symm_apply,
    resolventToDomain_spectralPencil hp _ z (by rwa [sourceResolventSet_eq] at hz), ContinuousLinearEquiv.symm_apply_apply]

/-- The coefficient-preserving inclusion of the original one-derivative domain. -/
def sourceDomainInclusion : WeightedCoeffPair (Weight.sobolev 1) p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    (domainInclusion.comp (WeightedCoeffPair.toMax (Weight.sobolev 1) p).toContinuousLinearMap)

theorem sourceResolvent_eq_inclusion_comp (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) :
    sourceResolvent hp φ z = sourceDomainInclusion.comp (sourceResolventToDomain hp φ z) := by
  ext a : 1
  change (CoeffPair.toMax p).symm (resolvent hp (CoeffPair.toMax p φ) z (CoeffPair.toMax p a)) =
    (CoeffPair.toMax p).symm (domainInclusion
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) p)
        ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm
          (resolventToDomain hp (CoeffPair.toMax p φ) z (CoeffPair.toMax p a)))))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem sourceDomainInclusion_fst_apply (a : WeightedCoeffPair (Weight.sobolev 1) p) (n : ℤ) :
    (sourceDomainInclusion a).fst n = a.fst.val n := scalarInclusion_apply a.fst n

@[simp] theorem sourceDomainInclusion_snd_apply (a : WeightedCoeffPair (Weight.sobolev 1) p) (n : ℤ) :
    (sourceDomainInclusion a).snd n = a.snd.val n := scalarInclusion_apply a.snd n

/-- The Zakharov–Shabat operator with both original finite source norms. -/
def sourceOperator (hp : p ≠ ⊤) (φ : CoeffPair p) :
    WeightedCoeffPair (Weight.sobolev 1) p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    ((operator hp (CoeffPair.toMax p φ)).comp
      (WeightedCoeffPair.toMax (Weight.sobolev 1) p).toContinuousLinearMap)

/-- The transported pencil is exactly lambda minus the original operator. -/
theorem sourceSpectralPencil_eq (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) :
    sourceSpectralPencil hp φ z = z • sourceDomainInclusion (p := p) - sourceOperator hp φ := by
  ext a : 1
  change (CoeffPair.toMax p).symm
    (spectralPencil hp (CoeffPair.toMax p φ) z (WeightedCoeffPair.toMax (Weight.sobolev 1) p a)) =
      z • (CoeffPair.toMax p).symm (domainInclusion (WeightedCoeffPair.toMax (Weight.sobolev 1) p a)) -
        (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p φ)
          (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))
  rw [spectralPencil_apply, map_sub, map_smul]

/-- Openness is preserved for the complete natural resolvent set. -/
theorem isOpen_sourceResolventSet (hp : p ≠ ⊤) (φ : CoeffPair p) : IsOpen (sourceResolventSet hp φ) := by
  rw [sourceResolventSet_eq]
  exact isOpen_resolventSet hp _

/-- The actual original-norm spectrum has the discrete subspace topology. -/
theorem discreteTopology_sourceResolventSet_compl (hp : p ≠ ⊤) (φ : CoeffPair p) :
    DiscreteTopology ↥((sourceResolventSet hp φ)ᶜ) := by
  rw [sourceResolventSet_eq]
  exact discreteTopology_periodicSpectrum hp _

/-- Free parameters belong to the full source resolvent set at zero potential. -/
theorem mem_sourceResolventSet_zero_of_notMem (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    z ∈ sourceResolventSet (p := p) hp 0 := by
  rw [sourceResolventSet_eq, map_zero]
  exact mem_resolventSet_zero_of_notMem hp z hz

/-- Compatibility with the actual original-norm free resolvent, including real parameters. -/
theorem sourceResolvent_zero_eq_free (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    sourceResolvent (p := p) hp 0 z = sourceFreeResolvent hp z hz := by
  unfold sourceResolvent
  rw [map_zero, resolvent_zero_eq_free hp z hz]
  rfl

end NLS.ZakharovShabat
