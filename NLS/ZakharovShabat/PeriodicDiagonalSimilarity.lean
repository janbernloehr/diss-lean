import NLS.ZakharovShabat.RootSpaces
import NLS.ZakharovShabat.PeriodOneEmbedding

/-! # Constant diagonal similarity of the periodic operator

Rescaling the second solution component by a nonzero constant conjugates
potentials (u,v) and (c u,c⁻¹ v). The actual domain, all root chains, and
algebraic multiplicities are transported, with no isometry assumption.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The same bounded invertible diagonal map acts on the base and on the domain. -/
def diagonalSimilarity (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂˣ) :
    (E × E) ≃L[ℂ] (E × E) :=
  (ContinuousLinearEquiv.refl ℂ E).prodCongr (c • ContinuousLinearEquiv.refl ℂ E)

@[simp] theorem diagonalSimilarity_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (c : ℂˣ) (f : E × E) :
    diagonalSimilarity E c f = (f.1,(c : ℂ) • f.2) := rfl

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reciprocal component rescaling of a coefficient potential. -/
def diagonalPotential (c : ℂˣ) : PairSpace p ≃L[ℂ] PairSpace p :=
  (c • ContinuousLinearEquiv.refl ℂ (Coeff p)).prodCongr
    (c⁻¹ • ContinuousLinearEquiv.refl ℂ (Coeff p))

@[simp] theorem diagonalPotential_apply (c : ℂˣ) (φ : PairSpace p) :
    diagonalPotential c φ = ((c : ℂ) • φ.1, (↑c⁻¹ : ℂ) • φ.2) := rfl

/-- Diagonal similarity respects the original one-derivative domain inclusion. -/
theorem domainInclusion_diagonalSimilarity (c : ℂˣ) (f : Domain p) :
    domainInclusion (diagonalSimilarity (ScalarDomain p) c f) =
      diagonalSimilarity (Coeff p) c (domainInclusion f) := by
  simp

/-- Exact conjugation of the original unbounded operator on its coefficient domain. -/
theorem operator_diagonalSimilarity (hp : p ≠ ⊤) (c : ℂˣ)
    (φ : PairSpace p) (f : Domain p) :
    operator hp φ (diagonalSimilarity (ScalarDomain p) c f) =
      diagonalSimilarity (Coeff p) c (operator hp (diagonalPotential c φ) f) := by
  apply Prod.ext <;> ext n
  · simp only [operator_fst_apply, diagonalSimilarity_apply, diagonalPotential_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, WeightedCoeff.smul_val]
    congr 1
    apply tsum_congr
    intro k
    ring
  · simp only [operator_snd_apply, diagonalSimilarity_apply, diagonalPotential_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, WeightedCoeff.smul_val]
    rw [mul_add, ← tsum_mul_left]
    congr 1
    · ring
    · apply tsum_congr
      intro k
      simp [← mul_assoc]

/-- Conjugation of z-L, including both domain and base transformations. -/
theorem spectralPencil_diagonalSimilarity (hp : p ≠ ⊤) (c : ℂˣ)
    (φ : PairSpace p) (z : ℂ) (f : Domain p) :
    spectralPencil hp φ z (diagonalSimilarity (ScalarDomain p) c f) =
      diagonalSimilarity (Coeff p) c (spectralPencil hp (diagonalPotential c φ) z f) := by
  simp only [spectralPencil_apply, domainInclusion_diagonalSimilarity,
    operator_diagonalSimilarity, map_sub, map_smul]

/-- The diagonal map identifies finite periodic root chains at every length. -/
theorem mem_periodicRootSpace_diagonalSimilarity (hp : p ≠ ⊤) (c : ℂˣ) (φ : PairSpace p)
    (z : ℂ) (n : ℕ) (x : PairSpace p) :
    diagonalSimilarity (Coeff p) c x ∈ periodicRootSpace hp φ z n ↔
      x ∈ periodicRootSpace hp (diagonalPotential c φ) z n := by
  induction n generalizing x with
  | zero =>
    change diagonalSimilarity (Coeff p) c x = 0 ↔ x = 0
    simpa only [map_zero] using
      ((diagonalSimilarity (Coeff p) c).injective.eq_iff (a := x) (b := 0))
  | succ n ih =>
    rw [mem_periodicRootSpace_succ, mem_periodicRootSpace_succ]
    constructor
    · rintro ⟨f, hf, hn⟩
      obtain ⟨g, rfl⟩ := (diagonalSimilarity (ScalarDomain p) c).surjective f
      rw [domainInclusion_diagonalSimilarity] at hf
      rw [spectralPencil_diagonalSimilarity] at hn
      exact ⟨g, (diagonalSimilarity (Coeff p) c).injective hf, (ih _).mp hn⟩
    · rintro ⟨f, hf, hn⟩
      refine ⟨diagonalSimilarity (ScalarDomain p) c f, ?_, ?_⟩
      · rw [domainInclusion_diagonalSimilarity, hf]
      · rw [spectralPencil_diagonalSimilarity]
        exact (ih _).mpr hn

/-- The same diagonal map identifies full periodic generalized root spaces. -/
theorem mem_periodicRootSpaceTop_diagonalSimilarity (hp : p ≠ ⊤) (c : ℂˣ) (φ : PairSpace p)
    (z : ℂ) (x : PairSpace p) :
    diagonalSimilarity (Coeff p) c x ∈ periodicRootSpaceTop hp φ z ↔
      x ∈ periodicRootSpaceTop hp (diagonalPotential c φ) z := by
  simp only [mem_periodicRootSpaceTop, mem_periodicRootSpace_diagonalSimilarity]

/-- Exact image identity for the full periodic generalized root space. -/
theorem map_periodicRootSpaceTop_diagonalSimilarity (hp : p ≠ ⊤) (c : ℂˣ) (φ : PairSpace p) (z : ℂ) :
    (periodicRootSpaceTop hp (diagonalPotential c φ) z).map
      (diagonalSimilarity (Coeff p) c).toLinearEquiv.toLinearMap = periodicRootSpaceTop hp φ z := by
  ext x
  obtain ⟨y, rfl⟩ := (diagonalSimilarity (Coeff p) c).surjective x
  rw [mem_periodicRootSpaceTop_diagonalSimilarity]
  constructor
  · rintro ⟨a, ha, he⟩
    exact (diagonalSimilarity (Coeff p) c).injective he ▸ ha
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- The original periodic full root spaces are diagonally conjugate. -/
def periodicRootSpaceTopDiagonalEquiv (hp : p ≠ ⊤) (c : ℂˣ) (φ : PairSpace p) (z : ℂ) :
    periodicRootSpaceTop hp (diagonalPotential c φ) z ≃ₗ[ℂ]
      periodicRootSpaceTop hp φ z :=
  (diagonalSimilarity (Coeff p) c).toLinearEquiv.ofSubmodules _ _
    (map_periodicRootSpaceTop_diagonalSimilarity hp c φ z)

/-- Diagonal similarity preserves the algebraic multiplicity of every original periodic eigenvalue. -/
theorem periodicAlgebraicMultiplicity_diagonalPotential (hp : p ≠ ⊤) (c : ℂˣ)
    (φ : PairSpace p) (z : ℂ) :
    periodicAlgebraicMultiplicity hp (diagonalPotential c φ) z =
      periodicAlgebraicMultiplicity hp φ z :=
  (periodicRootSpaceTopDiagonalEquiv hp c φ z).finrank_eq

/-- Diagonal similarity preserves the actual periodic spectral set. -/
theorem periodicSpectrum_diagonalPotential (hp : p ≠ ⊤) (c : ℂˣ) (φ : PairSpace p) :
    periodicSpectrum hp (diagonalPotential c φ) = periodicSpectrum hp φ := by
  ext z
  rw [← periodicAlgebraicMultiplicity_pos_iff hp (diagonalPotential c φ) z,
    periodicAlgebraicMultiplicity_diagonalPotential,
    periodicAlgebraicMultiplicity_pos_iff hp φ z]


end NLS.ZakharovShabat
