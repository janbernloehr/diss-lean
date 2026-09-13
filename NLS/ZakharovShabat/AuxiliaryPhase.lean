import NLS.ZakharovShabat.BoundaryOperators
import NLS.ZakharovShabat.PeriodicSpectrum

/-!
# The phase change for the auxiliary boundary problems

The source's auxiliary boundary vectors are obtained from the ordinary ones
by G(f₋,f₊)=(f₋,if₊). Conjugating the actual domain-to-base operator changes
the potential to (iφ₋,-iφ₊). Both maps preserve the coefficient norms exactly.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Rotate the positive component by i, in either the base or domain norm. -/
def auxiliaryPhase (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    (E × E) ≃ₗᵢ[ℂ] (E × E) where
  toFun f := (f.1,Complex.I • f.2)
  invFun f := (f.1,-Complex.I • f.2)
  map_add' f g := by simp [smul_add]
  map_smul' c f := Prod.ext rfl (smul_comm Complex.I c f.2)
  left_inv f := by simp [smul_smul]
  right_inv f := by simp [smul_smul]
  norm_map' f := by simp [Prod.norm_def, norm_smul]

@[simp] theorem auxiliaryPhase_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E × E) :
    auxiliaryPhase E f = (f.1,Complex.I • f.2) := rfl

@[simp] theorem auxiliaryPhase_symm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E × E) :
    (auxiliaryPhase E).symm f = (f.1,-Complex.I • f.2) := rfl

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The potential change in G⁻¹ L(φ) G, as an exact linear isometry. -/
def auxiliaryPotential : PairSpace p ≃ₗᵢ[ℂ] PairSpace p where
  toFun φ := (Complex.I • φ.1,-Complex.I • φ.2)
  invFun φ := (-Complex.I • φ.1,Complex.I • φ.2)
  map_add' φ ψ := by simp [smul_add]
  map_smul' c φ := Prod.ext (smul_comm Complex.I c φ.1) (smul_comm (-Complex.I) c φ.2)
  left_inv φ := by simp [smul_smul]
  right_inv φ := by simp [smul_smul]
  norm_map' φ := by simp [Prod.norm_def, norm_smul]

@[simp] theorem auxiliaryPotential_apply (φ : PairSpace p) :
    auxiliaryPotential φ = (Complex.I • φ.1,-Complex.I • φ.2) := rfl

@[simp] theorem auxiliaryPotential_symm_apply (φ : PairSpace p) :
    auxiliaryPotential.symm φ = (-Complex.I • φ.1,Complex.I • φ.2) := rfl

/-- Neumann-reflected potentials become Dirichlet-reflected after the phase change. -/
theorem auxiliaryPotential_mem_dirichlet_iff (φ : PairSpace p) :
    auxiliaryPotential φ ∈ dirichletSubspace ↔ φ ∈ neumannSubspace := by
  simp only [mem_dirichletSubspace, mem_neumannSubspace, auxiliaryPotential_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h n
    have hh := congrArg (fun z : ℂ => -Complex.I*z) (h n)
    simpa [← mul_assoc] using hh
  · intro h n
    rw [h n]
    ring

/-- The phase map commutes with the actual domain inclusion. -/
theorem domainInclusion_auxiliaryPhase (f : Domain p) :
    domainInclusion (auxiliaryPhase (ScalarDomain p) f) = auxiliaryPhase (Coeff p) (domainInclusion f) := by
  simp

/-- The exact coefficient operator conjugation, with the source's signs. -/
theorem operator_auxiliaryPhase (hp : p ≠ ⊤) (φ : PairSpace p) (f : Domain p) :
    operator hp φ (auxiliaryPhase (ScalarDomain p) f) =
      auxiliaryPhase (Coeff p) (operator hp (auxiliaryPotential φ) f) := by
  apply Prod.ext <;> ext n
  · simp only [operator_fst_apply, auxiliaryPhase_apply, auxiliaryPotential_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, WeightedCoeff.smul_val]
    congr 1
    apply tsum_congr
    intro k
    ring
  · simp only [operator_snd_apply, auxiliaryPhase_apply, auxiliaryPotential_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, WeightedCoeff.smul_val]
    rw [mul_add, ← tsum_mul_left]
    congr 1
    · ring
    · apply tsum_congr
      intro k
      simp [← mul_assoc]

/-- The corresponding identity for z-L, before restricting either boundary space. -/
theorem spectralPencil_auxiliaryPhase (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (f : Domain p) :
    spectralPencil hp φ z (auxiliaryPhase (ScalarDomain p) f) =
      auxiliaryPhase (Coeff p) (spectralPencil hp (auxiliaryPotential φ) z f) := by
  simp only [spectralPencil_apply, domainInclusion_auxiliaryPhase, operator_auxiliaryPhase, map_sub, map_smul]

/-- Phase transport preserves the actual eigenvalue equation between domain and base. -/
theorem eigenvector_auxiliaryPhase_iff (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (f : Domain p) :
    operator hp φ (auxiliaryPhase (ScalarDomain p) f) = z • domainInclusion (auxiliaryPhase (ScalarDomain p) f) ↔
      operator hp (auxiliaryPotential φ) f = z • domainInclusion f := by
  rw [operator_auxiliaryPhase, domainInclusion_auxiliaryPhase, ← map_smul,
    (auxiliaryPhase (Coeff p)).injective.eq_iff]

end NLS.ZakharovShabat
