import NLS.ZakharovShabat.SourceSpatialReflection
import NLS.ZakharovShabat.SourceComponentSwapSpectralData
import NLS.ZakharovShabat.SourceDiscriminantCotangent

/-! # Pure midpoint reflection of the physical source

The article's T reflects both fields without exchanging them. The older
`sourceSpatialReflection` combines midpoint reflection with component exchange;
composing it with P gives precisely T. All identities below hold on the entire
complex source space, with no reality or symmetry hypothesis on the potential.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pure midpoint reflection, with no component exchange. -/
def sourceMidpointReflection : CoeffPair p ≃ₗᵢ[ℂ] CoeffPair p :=
  sourceSpatialReflection.trans sourceComponentSwap

@[simp] theorem sourceMidpointReflection_fst (φ : CoeffPair p) :
    (sourceMidpointReflection φ).fst = Coeff.reflection φ.fst := rfl

@[simp] theorem sourceMidpointReflection_snd (φ : CoeffPair p) :
    (sourceMidpointReflection φ).snd = Coeff.reflection φ.snd := rfl

@[simp] theorem sourceMidpointReflection_involutive (φ : CoeffPair p) :
    sourceMidpointReflection (sourceMidpointReflection φ) = φ := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> simp

/-- T reflects the spectral parameter, exactly as P does. -/
theorem sourceDiscriminant_midpointReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential (sourceMidpointReflection φ)) (-z) =
      canonicalDiscriminant hp (periodOnePotential φ) z := by
  change canonicalDiscriminant hp
    (periodOnePotential (sourceComponentSwap (sourceSpatialReflection φ))) (-z) = _
  rw [sourceDiscriminant_componentSwap hp hp1,sourceDiscriminant_spatialReflection hp hp1]

/-- The spectral derivative has odd reflection parity. -/
theorem sourceDiscriminant_deriv_midpointReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    deriv (canonicalDiscriminant hp (periodOnePotential (sourceMidpointReflection φ))) (-z) =
      -deriv (canonicalDiscriminant hp (periodOnePotential φ)) z := by
  have he : (fun w : ℂ => canonicalDiscriminant hp
      (periodOnePotential (sourceMidpointReflection φ)) (-w)) =
      canonicalDiscriminant hp (periodOnePotential φ) :=
    funext (sourceDiscriminant_midpointReflection hp hp1 φ)
  have hd := ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
    (-z,sourceMidpointReflection φ) (mem_univ _)).comp
      (f := fun w : ℂ => (w,sourceMidpointReflection φ))
      (analyticAt_id.prod analyticAt_const)).differentiableAt.hasDerivAt
  have hc := hd.comp z (hasDerivAt_id z).neg
  have hc' : HasDerivAt (fun w : ℂ => canonicalDiscriminant hp
      (periodOnePotential (sourceMidpointReflection φ)) (-w))
      (deriv (canonicalDiscriminant hp
        (periodOnePotential (sourceMidpointReflection φ))) (-z)*(-1)) z := hc
  rw [he] at hc'
  have hval := hc'.deriv
  linear_combination hval

/-- Differentiate an exact discriminant symmetry as a source cotangent.
The transformation acts on directions by composition, so this formulation
retains the full Fréchet derivative without assuming a gradient model. -/
theorem sourceDiscriminantCotangent_of_linear_symmetry
    (hp : p ≠ ⊤) (hp1 : 1 < p) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (z w : ℂ)
    (hA : ∀ φ, canonicalDiscriminant hp (periodOnePotential (A φ)) w =
      canonicalDiscriminant hp (periodOnePotential φ) z) (φ : CoeffPair p) :
    sourceDiscriminantCotangent hp z φ =
      (sourceDiscriminantCotangent hp w (A φ)).comp A := by
  have hd := ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
    (w,A φ) (mem_univ _)).comp (f := fun ψ : CoeffPair p => (w,ψ))
    (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt
  have hc := hd.comp φ A.hasFDerivAt
  have he : (fun ψ : CoeffPair p =>
      canonicalDiscriminant hp (periodOnePotential (A ψ)) w) =
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) := funext hA
  change HasFDerivAt (fun ψ : CoeffPair p =>
    canonicalDiscriminant hp (periodOnePotential (A ψ)) w)
    ((sourceDiscriminantCotangent hp w (A φ)).comp A) φ at hc
  rw [he] at hc
  exact hc.fderiv

theorem sourceDiscriminantCotangent_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceDiscriminantCotangent hp z φ =
      (sourceDiscriminantCotangent hp (-z) (sourceComponentSwap φ)).comp
        sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap :=
  sourceDiscriminantCotangent_of_linear_symmetry hp hp1
    sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap z (-z)
    (fun ψ => sourceDiscriminant_componentSwap hp hp1 ψ z) φ

theorem sourceDiscriminantCotangent_midpointReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceDiscriminantCotangent hp z φ =
      (sourceDiscriminantCotangent hp (-z) (sourceMidpointReflection φ)).comp
        sourceMidpointReflection.toContinuousLinearEquiv.toContinuousLinearMap :=
  sourceDiscriminantCotangent_of_linear_symmetry hp hp1
    sourceMidpointReflection.toContinuousLinearEquiv.toContinuousLinearMap z (-z)
    (fun ψ => sourceDiscriminant_midpointReflection hp hp1 ψ z) φ

end NLS.ZakharovShabat
