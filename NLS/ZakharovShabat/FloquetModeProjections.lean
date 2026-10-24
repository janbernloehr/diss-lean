import NLS.ZakharovShabat.FloquetHyperbolicBasis

/-! # Algebraic mode projections for a two-dimensional Floquet eigenbasis -/
noncomputable section
set_option autoImplicit false
open Matrix Module
namespace NLS.ZakharovShabat

/-- Projection onto one vector of an actual Floquet eigenbasis. -/
def floquetModeProjection (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (i : Fin 2) :
    (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := (b.coord i).smulRight (b i)

@[simp] theorem floquetModeProjection_apply (b : Basis (Fin 2) ℂ (Fin 2 → ℂ))
    (i : Fin 2) (v : Fin 2 → ℂ) :
    floquetModeProjection b i v = b.repr v i • b i := rfl

/-- The two modes recover every initial vector. -/
theorem floquetModeProjection_add (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) :
    floquetModeProjection b 0 + floquetModeProjection b 1 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simpa only [Fin.sum_univ_two,LinearMap.add_apply,
    LinearMap.id_apply,floquetModeProjection_apply] using b.sum_repr v

/-- Each mode projection is idempotent. -/
theorem floquetModeProjection_idempotent (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (i : Fin 2) :
    (floquetModeProjection b i).comp (floquetModeProjection b i) = floquetModeProjection b i := by
  apply LinearMap.ext
  intro v
  simp [floquetModeProjection_apply ]

/-- Different modes annihilate each other. -/
theorem floquetModeProjection_comp_eq_zero (b : Basis (Fin 2) ℂ (Fin 2 → ℂ))
    (i j : Fin 2) (hij : i ≠ j) :
    (floquetModeProjection b i).comp (floquetModeProjection b j) = 0 := by
  apply LinearMap.ext
  intro v
  simp [floquetModeProjection_apply,hij]

/-- Monodromy acts on each projected input by its own multiplier. -/
theorem mulVec_floquetModeProjection (M : Matrix (Fin 2) (Fin 2) ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ)
    (hM : ∀ i, M *ᵥ b i = μ i • b i) (i : Fin 2) (v : Fin 2 → ℂ) :
    M *ᵥ floquetModeProjection b i v = μ i • floquetModeProjection b i v := by
  rw [floquetModeProjection_apply,Matrix.mulVec_smul,hM]
  module

/-- Projecting after monodromy gives the same scalar mode action. -/
theorem floquetModeProjection_mulVec (M : Matrix (Fin 2) (Fin 2) ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ)
    (hM : ∀ i, M *ᵥ b i = μ i • b i) (i : Fin 2) (v : Fin 2 → ℂ) :
    floquetModeProjection b i (M *ᵥ v) = μ i • floquetModeProjection b i v := by
  have he : (floquetModeProjection b i).comp M.mulVecLin = μ i • floquetModeProjection b i := by
    apply b.ext
    intro j
    by_cases hij : i = j
    · subst j
      simp [hM,floquetModeProjection_apply]
    · simp [hM,floquetModeProjection_apply,hij]
  exact LinearMap.congr_fun he v

end NLS.ZakharovShabat
