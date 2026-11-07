import NLS.ZakharovShabat.L2PhysicalGradientUniqueness
import NLS.ZakharovShabat.SourceFullAbelianDifferentialData
import NLS.ZakharovShabat.L2SourceCharacteristicGradients
import NLS.ZakharovShabat.L2NormalizedNonlocalGradient

/-! # The actual full primitive has the normalized physical gradient

The full source derivative of the constructed primitive is represented in
all original Hilbert directions by the canonical-root-normalized whole-line
discriminant gradient. The source and spectral domains are the actual common
open neighborhood and its moving cut complement, not a formal primitive.
-/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.ZakharovShabat

/-- The physical field representing the actual full Abelian primitive's
source derivative. It is independent of the primitive's integer constant. -/
def sourceFullAbelianPhysicalGradient (φ : CoeffPair 2) (z : ℂ) : ℝ → ℂ × ℂ :=
  l2NormalizedDiscriminantGradient (sourcePhysicalL2 φ) z
    (sourceCanonicalRoot (by simp) (by norm_num) φ z)

theorem continuous_sourceFullAbelianPhysicalGradient (φ : CoeffPair 2) (z : ℂ) :
    Continuous (sourceFullAbelianPhysicalGradient φ z) := by
  unfold sourceFullAbelianPhysicalGradient l2NormalizedDiscriminantGradient
  exact (continuous_l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z).const_smul
    (sourceCanonicalRoot (by simp) (by norm_num) φ z)⁻¹

theorem periodic_sourceFullAbelianPhysicalGradient (φ : CoeffPair 2) (z : ℂ) :
    Function.Periodic (sourceFullAbelianPhysicalGradient φ z) 1 := by
  intro x
  unfold sourceFullAbelianPhysicalGradient l2NormalizedDiscriminantGradient
  rw [periodic_l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z x]

/-- Equality of the actual Frechet derivative with its physical bilinear
integral, for every original L2 direction and every point off the moving cuts. -/
theorem sourceFullAbelianPrimitive_fderiv_eq_physical_integral
    {W U : Set (CoeffPair 2)}
    (D : SourceFullAbelianDifferentialData (by simp) (by norm_num) W U)
    (j : ℤ) (φ h : CoeffPair 2) (hφ : φ ∈ U) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ) :
    (fderiv ℂ (fun χ => sourceFullAbelianPrimitive (by simp) (by norm_num) W j (z,χ)) φ) h =
      ∫ x in (0:ℝ)..1,
        (sourceFullAbelianPhysicalGradient φ z x).1*(sourcePhysicalL2 h).ofLp.1 x+
        (sourceFullAbelianPhysicalGradient φ z x).2*(sourcePhysicalL2 h).ofLp.2 x := by
  rw [D.source_fderiv j z φ hφ hz,smul_apply,smul_eq_mul,
    sourceDiscriminantCotangent_apply_eq_l2,fderiv_l2Discriminant_eq_gradient_integral,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0:ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
  simp only [sourceFullAbelianPhysicalGradient,l2NormalizedDiscriminantGradient,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
    l2WholeLineDiscriminantGradient_on_unit _ _ ⟨x,hx'⟩]
  ring

/-- Every continuous periodic representative of the same actual full source
cotangent agrees pointwise, including all period seams. -/
theorem sourceFullAbelianPhysicalGradient_unique
    {W U : Set (CoeffPair 2)}
    (D : SourceFullAbelianDifferentialData (by simp) (by norm_num) W U)
    (j : ℤ) (φ : CoeffPair 2) (hφ : φ ∈ U) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ)
    (g : ℝ → ℂ × ℂ) (hg : Continuous g) (hpg : Function.Periodic g 1)
    (h : ∀ v : CoeffPair 2,
      (fderiv ℂ (fun χ => sourceFullAbelianPrimitive (by simp) (by norm_num) W j (z,χ)) φ) v =
        ∫ x in (0:ℝ)..1, (g x).1*(sourcePhysicalL2 v).ofLp.1 x+
          (g x).2*(sourcePhysicalL2 v).ofLp.2 x) :
    g = sourceFullAbelianPhysicalGradient φ z := by
  apply eq_of_continuous_periodic_physical_L2_pairings g _ hg
    (continuous_sourceFullAbelianPhysicalGradient φ z) hpg
    (periodic_sourceFullAbelianPhysicalGradient φ z)
  intro u
  have h₁ := h (sourcePhysicalL2Equiv.symm u)
  have h₂ := sourceFullAbelianPrimitive_fderiv_eq_physical_integral D j φ
    (sourcePhysicalL2Equiv.symm u) hφ z hz
  simp only [sourcePhysicalL2_equiv_symm] at h₁ h₂
  exact h₁.symm.trans h₂

end NLS.ZakharovShabat
