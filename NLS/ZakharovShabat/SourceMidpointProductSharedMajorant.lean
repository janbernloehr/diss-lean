import NLS.SequenceSpaces.UniformReciprocalMajorant
import NLS.ZakharovShabat.SourceMidpointProductCutoffLimit
import NLS.ZakharovShabat.SourceStandardRootGapSideSource

/-! # Shared midpoint-product bounds for varying root rows

The numerator displacement is a fixed weight sequence times a uniformly
bounded lp row. Holder and powered Young give one absolute reciprocal
majorant before that row is chosen. A uniform exponential estimate for
the product remainder preserves this same majorant on the selected discs.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- The reciprocal-kernel constant used by the shared midpoint bound. -/
def sourceSharedMidpointKernelNorm (hp : p ≠ ⊤) (hr1 : 1 < r) : ℝ :=
  ‖Coeff.puncturedLattice (min r p.conjExponent)
    (lt_min hr1 ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))‖

/-- A uniform norm bound depending only on the separation constant,
row bound, weight bound, and the two sequence exponents. -/
def sourceSharedMidpointMajorantBound (hp : p ≠ ⊤) (hr1 : 1 < r) (C A G : ℝ) : ℝ :=
  let κ := sourceSharedMidpointKernelNorm hp hr1
  let U := C*A*G*κ
  (C*A)*(1+Real.exp U*U)*G*κ

/-- A single lr sequence controls every midpoint product with a fixed
weight g and any lp multiplier row of norm at most A. It is uniform in
the spectral point and selected index, with an explicit source-independent constant. -/
theorem exists_sourceMidpointProduct_sharedMajorant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hr : r ≠ ⊤) (hr1 : 1 < r)
    (φ ψ : CoeffPair p) (N : ℕ) (ε C A G : ℝ) (hC : 1 ≤ C) (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hsep : ∀ k j : ℤ, k ≠ j → ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε k,
      |((k-j:ℤ):ℝ)| ≤ C*‖sourceStandardRootMidpoint hp hp1 ψ j-z‖)
    (g : Coeff r) (hg : ‖g‖ ≤ G) :
    ∃ B : Coeff r, ‖B‖ ≤ sourceSharedMidpointMajorantBound hp hr1 C A G ∧
      ∀ α : Coeff p, ‖α‖ ≤ A → ∀ β : Coeff p, (∀ j, β j = g j*α j) →
        ∀ k : ℤ, ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε k,
          ‖sourceMidpointProductRow hp hp1 ψ β k z‖ ≤ ‖B k‖ := by
  obtain ⟨D,hD,hrows⟩ := Coeff.exists_uniform_reciprocal_majorant hp hp1 hr hr1 g
  let κ := sourceSharedMidpointKernelNorm hp hr1
  have hκ : 0 ≤ κ := by
    dsimp [κ,sourceSharedMidpointKernelNorm]
    exact lp.norm_nonneg' _
  have hC0 : 0 ≤ C := by linarith
  have hDG : ‖D‖ ≤ G*κ := hD.trans (mul_le_mul_of_nonneg_right hg hκ)
  let U := C*A*G*κ
  have hU : 0 ≤ U := by dsimp [U]; positivity
  let L := (C*A)*(1+Real.exp U*U)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let B : Coeff r := (L:ℂ) • D
  refine ⟨B,?_,?_⟩
  · calc
      ‖B‖ = L*‖D‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hL]
      _ ≤ L*(G*κ) := mul_le_mul_of_nonneg_left hDG hL
      _ = _ := by dsimp [L,U,κ,sourceSharedMidpointMajorantBound]; ring
  intro α hα β hβ k z hz
  let u (j : ℤ) := if j = k then (0:ℂ) else β j/(sourceStandardRootMidpoint hp hp1 ψ j-z)
  let v (j : ℤ) := if j = k then (0:ℝ) else ‖g j‖*‖α j‖/|((k-j:ℤ):ℝ)|
  obtain ⟨hv,hvbound⟩ := hrows α k
  have hpoint (j : ℤ) : ‖u j‖ ≤ C*v j := by
    by_cases hj : j = k
    · simp only [u,v,if_pos hj,norm_zero,mul_zero,le_refl]
    · have hb := norm_midpoint_displacement_div_le C hC k j (Ne.symm hj) (β j)
        (sourceStandardRootMidpoint hp hp1 ψ j) z (hsep k j (Ne.symm hj) z hz)
      have habs : |((j-k:ℤ):ℝ)| = |((k-j:ℤ):ℝ)| := by
        rw [show j-k = -(k-j) by ring,Int.cast_neg,abs_neg]
      simpa only [u,v,if_neg hj,hβ j,norm_mul,habs] using hb
  have hu : Summable (fun j => ‖u j‖) :=
    (hv.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  let S := ∑' j, ‖u j‖
  have hS0 : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  have hSD : S ≤ C*A*‖D k‖ := by
    calc
      S ≤ ∑' j, C*v j := hu.tsum_le_tsum hpoint (hv.mul_left C)
      _ = C*∑' j, v j := tsum_mul_left
      _ ≤ C*(‖α‖*‖D k‖) := mul_le_mul_of_nonneg_left hvbound hC0
      _ ≤ C*A*‖D k‖ := by nlinarith [mul_le_mul_of_nonneg_right hα (norm_nonneg (D k))]
  have hSU : S ≤ U := hSD.trans (by
    dsimp [U]
    have hk := (lp.norm_apply_le_norm (zero_lt_one.trans hr1).ne' D k).trans hDG
    nlinarith [mul_le_mul_of_nonneg_left hk (mul_nonneg hC0 hA)])
  have hprod := NLS.ComplexAnalysis.norm_tprod_one_add_sub_one_le_linear_add_square u hu hSU
  have hlin := norm_tsum_le_tsum_norm hu
  have hquad : S^2 ≤ U*S := by nlinarith
  have hmajor : ‖(∏' j, (1+u j))-1‖ ≤ L*‖D k‖ := by
    calc
      _ ≤ S+Real.exp U*S^2 := hprod.trans (add_le_add hlin le_rfl)
      _ ≤ (1+Real.exp U*U)*S := by nlinarith [mul_le_mul_of_nonneg_left hquad (Real.exp_pos U).le]
      _ ≤ (1+Real.exp U*U)*(C*A*‖D k‖) := mul_le_mul_of_nonneg_left hSD (by positivity)
      _ = _ := by dsimp [L]; ring
  change ‖(∏' j, (1+u j))-1‖ ≤ ‖(L:ℂ) • D k‖
  simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hL] using hmajor

end NLS.ZakharovShabat
