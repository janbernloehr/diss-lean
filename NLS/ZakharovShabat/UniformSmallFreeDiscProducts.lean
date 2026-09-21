import NLS.Fourier.UniformSmallRelativeProducts
import NLS.ZakharovShabat.FreeDiscProductMajorant

/-! # Uniform smallness of relative products on free spectral discs
Rescaling by pi transfers the small-tail estimate to the spectral lattice.
The index threshold is common to every point of every distant closed disc.
-/

noncomputable section
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Bounded displacements with small tails give uniformly small free-disc product errors. -/
theorem exists_uniform_small_freeDiscRelativeProducts (hp : p ≠ ⊤) (hp1 : 1 < p)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Finset ℤ, ∃ N : ℕ, ∀ a : Coeff p,
      ‖a‖ ≤ R → ‖a-Coeff.truncate s a‖ ≤ δ →
      ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
        ‖freeDiscRelativeProduct a n z-1‖ < ε := by
  obtain ⟨δ,hδ,h⟩ := exists_uniform_small_sampledProductErrors hp1 hp (div_nonneg hR Real.pi_pos.le) hε
  refine ⟨Real.pi*δ,mul_pos Real.pi_pos hδ,fun s => ?_⟩
  obtain ⟨N,hN⟩ := h s
  refine ⟨N,fun a ha ht n hn z hz => ?_⟩
  let b : Coeff p := (Real.pi : ℂ)⁻¹ • a
  have hb : ‖b‖ ≤ R/Real.pi := by
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr Real.pi_pos.le)
  have hbt : ‖b-Coeff.truncate s b‖ ≤ δ := by
    dsimp [b]
    rw [Coeff.truncate_smul,← smul_sub,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    calc
      _ ≤ Real.pi⁻¹*(Real.pi*δ) := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr Real.pi_pos.le)
      _ = δ := by rw [← mul_assoc,inv_mul_cancel₀ Real.pi_ne_zero,one_mul]
  let w : ℤ → ℂ := fun k => (Real.pi : ℂ)*k+(z-(Real.pi : ℂ)*n)
  have hw (k : ℤ) : ‖w k-(Real.pi : ℂ)*k‖ ≤ Real.pi/2 := by simpa [w] using hz
  have he := hN b hb hbt (freeSampleDisplacement w) (norm_freeSampleDisplacement_le w hw) n hn
  change ‖freeDiscProductError hp1 hp a w hw n‖ < ε at he
  rw [freeDiscProductError_apply] at he
  simpa [freeDiscRelativeProduct,w] using he

end NLS.ZakharovShabat
