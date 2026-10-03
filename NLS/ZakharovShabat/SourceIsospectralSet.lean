import NLS.ZakharovShabat.PeriodicDiscriminantSpectralData
import NLS.ZakharovShabat.SourceActionTorus
import NLS.ZakharovShabat.SourceActionExponentDifferential

/-! # Actual isospectral sets, their action tori, and compactness

Isospectrality retains the original coefficient-space periodic spectrum
and its algebraic multiplicities. It is equivalent to equality of the
normalized discriminant, hence defines a closed source set. Common
spectral data give common canonical roots and original actions. This
proves the torus inclusion for all finite exponents above one, and
compactness of the actual isospectral set for exponents at most two.
The converse torus inclusion remains a separate step of Lemma 17.5.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual periodic isospectral set, including algebraic multiplicities. -/
def sourceIsospectralSet (hp : p ≠ ⊤) (φ : realTypeSourceSubmodule p) :
    Set (realTypeSourceSubmodule p) :=
  {ψ | periodicSpectrum hp (periodOnePotential ψ.val) = periodicSpectrum hp (periodOnePotential φ.val) ∧
    ∀ z : ℂ, periodicAlgebraicMultiplicity hp (periodOnePotential ψ.val) z =
      periodicAlgebraicMultiplicity hp (periodOnePotential φ.val) z}

/-- Original spectral isospectrality is exactly equality of normalized discriminants. -/
theorem mem_sourceIsospectralSet_iff_discriminant_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) :
    ψ ∈ sourceIsospectralSet hp φ ↔
      canonicalDiscriminant hp (periodOnePotential ψ.val) =
        canonicalDiscriminant hp (periodOnePotential φ.val) := by
  constructor
  · intro h
    exact canonicalDiscriminant_eq_of_spectral_data hp hp1 _ _
      (periodOnePotential_mem _) (periodOnePotential_mem _)
      (isRealType_periodOnePotential ψ.val ψ.property) (isRealType_periodOnePotential φ.val φ.property)
      h.1 h.2
  · exact periodic_spectral_data_eq_of_discriminant_eq hp hp1 _ _
      (periodOnePotential_mem _) (periodOnePotential_mem _)

/-- The original periodic isospectral set is closed in the source norm. -/
theorem isClosed_sourceIsospectralSet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) : IsClosed (sourceIsospectralSet hp φ) := by
  have he : sourceIsospectralSet hp φ =
      {ψ : realTypeSourceSubmodule p | ∀ z : ℂ, canonicalDiscriminant hp (periodOnePotential ψ.val) z =
        canonicalDiscriminant hp (periodOnePotential φ.val) z} := by
    ext ψ
    exact (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).trans funext_iff
  rw [he,ofPred_forall]
  apply isClosed_iInter
  intro z
  have hc : Continuous (fun t : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential t.2) t.1) :=
    continuousOn_univ.mp (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1).continuousOn
  have hpair : Continuous (fun ψ : realTypeSourceSubmodule p => (z,ψ.val)) :=
    continuous_const.prodMk continuous_subtype_val
  have hcomp := hc.comp (f := fun ψ : realTypeSourceSubmodule p => (z,ψ.val)) hpair
  exact isClosed_eq hcomp continuous_const

/-- The same original spectral data give the same canonically normalized
square root, with its sign and every signed index retained. -/
theorem sourceCanonicalRoot_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (z : ℂ) :
    sourceCanonicalRoot hp hp1 ψ.val z = sourceCanonicalRoot hp hp1 φ.val z := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val) (periodOnePotential_mem _) (periodOnePotential_mem _)
    h.1 h.2
  have he (n : ℤ) (w : ℂ) : sourceStandardRoot hp hp1 ψ.val n w = sourceStandardRoot hp hp1 φ.val n w := by
    unfold sourceStandardRoot canonicalPeriodicMidpoint canonicalPeriodicGap
    rw [hl,hr]
  simp only [sourceCanonicalRoot,sourceStandardRootPairedProduct,sourceStandardRootPairedFactor,he]

/-- The actual action-circle integrals are invariant under isospectrality. -/
theorem sourceActionCircle_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (c : ℂ) (R : ℝ) :
    sourceActionCircle hp hp1 ψ.val c R = sourceActionCircle hp hp1 φ.val c R := by
  have hΔ := (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mp h
  simp only [sourceActionCircle,sourceCriticalRootRatioJoint,hΔ,
    sourceCanonicalRoot_eq_of_isospectral hp hp1 φ ψ h]

/-- Every original indexed complex action agrees on an actual isospectral set,
including closed gaps and the finite central block. -/
theorem sourceRealAction_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) :
    sourceRealAction hp hp1 ψ.val ψ.property n = sourceRealAction hp hp1 φ.val φ.property n := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val) (periodOnePotential_mem _) (periodOnePotential_mem _)
    h.1 h.2
  let ε := sourceRealActionEpsilon hp hp1 ψ.val ψ.property n
  let ε' := sourceRealActionEpsilon hp hp1 φ.val φ.property n
  have hε : 0 < ε := (sourceRealActionEpsilon_spec hp hp1 ψ.val ψ.property n).1
  have hε' : 0 < ε' := (sourceRealActionEpsilon_spec hp hp1 φ.val φ.property n).1
  let η := min ε ε'/2
  have hη : 0 < η := half_pos (lt_min hε hε')
  have hηψ : η ∈ Ioc 0 ε := ⟨hη,by dsimp [η]; linarith [min_le_left ε ε']⟩
  have hηφ : η ∈ Ioc 0 ε' := ⟨hη,by dsimp [η]; linarith [min_le_right ε ε']⟩
  have hψ := sourceRealAction_eq_small_midpointCircle hp hp1 ψ.val ψ.property n hηψ
  have hφ := sourceRealAction_eq_small_midpointCircle hp hp1 φ.val φ.property n hηφ
  dsimp only at hψ hφ
  rw [hl,hr,sourceActionCircle_eq_of_isospectral hp hp1 φ ψ h] at hψ
  exact hψ.trans hφ.symm

/-- The actual isospectral set lies in the level set of every original action. -/
theorem sourceIsospectralSet_subset_actionLevelSet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) : sourceIsospectralSet hp φ ⊆ sourceRealActionLevelSet hp hp1 φ :=
  fun ψ h n => congrArg Complex.re (sourceRealAction_eq_of_isospectral hp hp1 φ ψ h n)

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Lemma 17.5(ii), in the stronger range of all finite `p > 1`:
the actual isospectral image lies in the prescribed action torus. -/
theorem image_isospectralSet_subset_actionTorus
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceSubmodule p) :
    sourceRealBirkhoffMap hp hp1 s '' sourceIsospectralSet hp φ ⊆
      RealCoeff.actionTorus p (fun n => (sourceRealAction hp hp1 φ.val φ.property n).re) :=
  (image_mono (sourceIsospectralSet_subset_actionLevelSet hp hp1 φ)).trans
    (D.image_actionLevelSet_subset_actionTorus φ)

/-- The actual periodic isospectral set is compact in the original source
norm for `1 < p ≤ 2`, without a finite-gap hypothesis. -/
theorem isCompact_isospectralSet
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) : IsCompact (sourceIsospectralSet hp φ) :=
  (D.isCompact_actionLevelSet hp2 φ).of_isClosed_subset
    (isClosed_sourceIsospectralSet hp hp1 φ) (sourceIsospectralSet_subset_actionLevelSet hp hp1 φ)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
