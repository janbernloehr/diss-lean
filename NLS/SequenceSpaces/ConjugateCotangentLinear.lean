import NLS.SequenceSpaces.ConjugateCotangent
import NLS.Poisson.SourceHamiltonianDirection

/-! # Continuous conjugate-exponent recovery of cotangents

The previously recovered conjugate coefficients depend continuously and
linearly on the functional. Applied to source pairs, this gives the
Hamiltonian direction in the conjugate exponent, with the original
reflection and Poisson signs.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
namespace Coeff

/-- The conjugate coefficient representative as a bounded linear operation. -/
def conjugateCotangentCLM (hq : q ≠ ⊤) (hp : p ≠ ⊤) :
    (Coeff q →L[ℂ] ℂ) →L[ℂ] Coeff p :=
  LinearMap.mkContinuous {
    toFun := conjugateCotangent hq hp
    map_add' := by
      intro L M
      ext n
      simp only [conjugateCotangent_apply,add_apply,lp.coeFn_add,Pi.add_apply]
    map_smul' := by
      intro z L
      ext n
      simp only [conjugateCotangent_apply,smul_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
  } 1 (by intro L; simpa only [one_mul] using! norm_conjugateCotangent_le hq hp L)

@[simp] theorem conjugateCotangentCLM_apply (hq : q ≠ ⊤) (hp : p ≠ ⊤)
    (L : Coeff q →L[ℂ] ℂ) (n : ℤ) :
    conjugateCotangentCLM hq hp L n = L (lp.single q n 1) := conjugateCotangent_apply hq hp L n

@[simp] theorem norm_conjugateCotangentCLM (hq : q ≠ ⊤) (hp : p ≠ ⊤)
    (L : Coeff q →L[ℂ] ℂ) : ‖conjugateCotangentCLM hq hp L‖ = ‖L‖ :=
  norm_conjugateCotangent hq hp L

end Coeff
namespace CoeffPair

/-- Both conjugate coefficient sequences of a source cotangent. -/
def conjugateCotangentCoefficients (hq : q ≠ ⊤) (hp : p ≠ ⊤) :
    (CoeffPair q →L[ℂ] ℂ) →L[ℂ] (Coeff p × Coeff p) :=
  ((Coeff.conjugateCotangentCLM hq hp).comp
    ((ContinuousLinearMap.compL ℂ (Coeff q) (CoeffPair q) ℂ).flip inlCLM)).prod
  ((Coeff.conjugateCotangentCLM hq hp).comp
    ((ContinuousLinearMap.compL ℂ (Coeff q) (CoeffPair q) ℂ).flip inrCLM))

@[simp] theorem conjugateCotangentCoefficients_fst (hq : q ≠ ⊤) (hp : p ≠ ⊤)
    (L : CoeffPair q →L[ℂ] ℂ) (n : ℤ) :
    (conjugateCotangentCoefficients hq hp L).1 n = L (inlCLM (lp.single q n 1)) :=
  Coeff.conjugateCotangentCLM_apply hq hp (L.comp inlCLM) n

@[simp] theorem conjugateCotangentCoefficients_snd (hq : q ≠ ⊤) (hp : p ≠ ⊤)
    (L : CoeffPair q →L[ℂ] ℂ) (n : ℤ) :
    (conjugateCotangentCoefficients hq hp L).2 n = L (inrCLM (lp.single q n 1)) :=
  Coeff.conjugateCotangentCLM_apply hq hp (L.comp inrCLM) n

end CoeffPair
namespace Poisson

/-- A source cotangent at exponent `q` has its actual Hamiltonian
coefficient pair at conjugate exponent `p`. -/
def conjugateHamiltonianDirection (hq : q ≠ ⊤) (hp : p ≠ ⊤) :
    (CoeffPair q →L[ℂ] ℂ) →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    (((-I) • (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp
        (CoeffPair.conjugateCotangentCoefficients hq hp)))).prod
    (I • (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp
        (CoeffPair.conjugateCotangentCoefficients hq hp)))))

@[simp] theorem conjugateHamiltonianDirection_fst (hq : q ≠ ⊤) (hp : p ≠ ⊤)
    (L : CoeffPair q →L[ℂ] ℂ) (n : ℤ) :
    (conjugateHamiltonianDirection hq hp L).fst n = -I*L (CoeffPair.inrCLM (lp.single q (-n) 1)) := by
  change (-I) * (CoeffPair.conjugateCotangentCoefficients hq hp L).2 (-n) = _
  rw [CoeffPair.conjugateCotangentCoefficients_snd]

@[simp] theorem conjugateHamiltonianDirection_snd (hq : q ≠ ⊤) (hp : p ≠ ⊤)
    (L : CoeffPair q →L[ℂ] ℂ) (n : ℤ) :
    (conjugateHamiltonianDirection hq hp L).snd n = I*L (CoeffPair.inlCLM (lp.single q (-n) 1)) := by
  change I * (CoeffPair.conjugateCotangentCoefficients hq hp L).1 (-n) = _
  rw [CoeffPair.conjugateCotangentCoefficients_fst]

/-- Inclusion of the recovered direction into Hilbert space is exactly
the Hamiltonian of the original functional restricted to Hilbert sources. -/
theorem conjugateHamiltonianDirection_hilbert_inclusion
    (hq : q ≠ ⊤) (hp : p ≠ ⊤) (hp2 : p ≤ 2) (h2q : 2 ≤ q)
    (L : CoeffPair q →L[ℂ] ℂ) :
    CoeffPair.exponentInclusion hp2 (conjugateHamiltonianDirection hq hp L) =
      sourceHamiltonianDirection (le_refl 2) (L.comp (CoeffPair.exponentInclusion h2q)) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n
  · change (conjugateHamiltonianDirection hq hp L).fst n = _
    rw [conjugateHamiltonianDirection_fst]
    change -I*L (CoeffPair.inrCLM (lp.single q (-n) 1)) =
      -I*(CoeffPair.cotangentCoefficients (le_refl 2) (L.comp (CoeffPair.exponentInclusion h2q))).2 (-n)
    rw [CoeffPair.cotangentCoefficients_snd]
    rfl
  · change (conjugateHamiltonianDirection hq hp L).snd n = _
    rw [conjugateHamiltonianDirection_snd]
    change I*L (CoeffPair.inlCLM (lp.single q (-n) 1)) =
      I*(CoeffPair.cotangentCoefficients (le_refl 2) (L.comp (CoeffPair.exponentInclusion h2q))).1 (-n)
    rw [CoeffPair.cotangentCoefficients_fst]
    rfl

end Poisson
end NLS
