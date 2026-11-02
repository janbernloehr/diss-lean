import NLS.KdV.PseudomeasureBilinearSymmetry
import NLS.KdV.PseudomeasureSpectralLipschitz

/-! # Separation of the actual singular endpoint determinant roots

The equality of the actual diagonal corrections and the proved spectral
Lipschitz estimate imply the source's constant-six squared separation bound.
The supremum is over the entire corrected closed strip. No square-root
branch, real-potential hypothesis, spectral label or assumed gap estimate
is used.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 1 ≤ n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

include hn hs in
/-- The actual source determinant has the equal-diagonal scalar factorization. -/
theorem endpointReducedDeterminant_factorization (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    endpointReducedDeterminant r hr hr1 n (q,z) =
      (z-(freeHillValue n:ℂ)-endpointDiagonal r hr hr1 n (q,z))^2 -
        endpointUpperCoupling r hr hr1 n (q,z)*endpointLowerCoupling r hr hr1 n (q,z) := by
  unfold endpointReducedDeterminant endpointDiagonal endpointUpperCoupling endpointLowerCoupling
  rw [endpointReducedFamily_eq r hr hr1 n hn (q,z) hz hs,
    endpointEffectiveFamily_eq r hr hr1 n hn (q,z) hz hs,
    FiniteSpectralDeterminant.det_prod_formula]
  have he := endpointHillEffectivePotential_diagonals_eq r hr hr1 n hn z hz q hs
  change ((z-(freeHillValue n:ℂ))*1 -
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)).val n) *
    ((z-(freeHillValue n:ℂ))*1 -
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)).val (-(n:ℤ))) -
    (((z-(freeHillValue n:ℂ))*0 -
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)).val n) *
    ((z-(freeHillValue n:ℂ))*0 -
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)).val (-(n:ℤ)))) = _
  rw [← he]
  ring

/-- The actual coupling radius, uniformly over the whole closed high strip. -/
def endpointCouplingRadius : ℝ :=
  sSup ((fun z : ℂ => Real.sqrt ‖endpointUpperCoupling r hr hr1 n (q,z)*
    endpointLowerCoupling r hr hr1 n (q,z)‖) '' reducedHillStrip n)

include hn hs in
/-- The coupling supremum is finite, with the proved endpoint growth bound. -/
theorem bddAbove_endpointCouplingRadii :
    BddAbove ((fun z : ℂ => Real.sqrt ‖endpointUpperCoupling r hr hr1 n (q,z)*
      endpointLowerCoupling r hr hr1 n (q,z)‖) '' reducedHillStrip n) := by
  have hW := ((Weight.sobolev r).positive (2*(n:ℤ))).le
  refine ⟨2*Weight.sobolev r (2*(n:ℤ))*‖q‖, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have h1 := (endpointHillEffectiveCorrection_columns_le r hr hr1 n hn z hz q hs).1
  have h2 := (endpointHillEffectiveCorrection_columns_le r hr hr1 n hn z hz q hs).2
  have hplus : ‖endpointUpperCoupling r hr hr1 n (q,z)‖ ≤
      2*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
    unfold endpointUpperCoupling
    rw [endpointEffectiveFamily_eq r hr hr1 n hn (q,z) hz hs]
    exact (norm_fst_le _).trans h2
  have hminus : ‖endpointLowerCoupling r hr hr1 n (q,z)‖ ≤
      2*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
    unfold endpointLowerCoupling
    rw [endpointEffectiveFamily_eq r hr hr1 n hn (q,z) hz hs]
    exact (norm_snd_le _).trans h1
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) ((Weight.sobolev r).positive _).le) (norm_nonneg q), ?_⟩
  rw [norm_mul, pow_two]
  exact mul_le_mul hplus hminus (norm_nonneg _) (by positivity)

include hn hs in
/-- Each coupling product is controlled by the actual full-strip supremum. -/
theorem sqrt_endpointCouplingProduct_le_radius (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    Real.sqrt ‖endpointUpperCoupling r hr hr1 n (q,z)*endpointLowerCoupling r hr hr1 n (q,z)‖ ≤
      endpointCouplingRadius r hr hr1 n q :=
  le_csSup (bddAbove_endpointCouplingRadii r hr hr1 n hn q hs) ⟨z, hz, rfl⟩

include hn hs in
/-- The full-strip coupling radius is nonnegative, including at the zero potential. -/
theorem endpointCouplingRadius_nonneg : 0 ≤ endpointCouplingRadius r hr hr1 n q := by
  have hz : (freeHillValue n:ℂ) ∈ reducedHillStrip n := by
    change |(freeHillValue n:ℂ).re-freeHillValue n| ≤ 6*(n:ℝ)
    simp only [Complex.ofReal_re, sub_self, abs_zero]
    positivity
  exact (Real.sqrt_nonneg _).trans
    (sqrt_endpointCouplingProduct_le_radius r hr hr1 n hn q hs (freeHillValue n:ℂ) hz)

include hn hs in
/-- At a determinant zero, the exact shifted distance is bounded by the coupling radius. -/
theorem endpointReduced_root_shift_bound (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hd : endpointReducedDeterminant r hr hr1 n (q,z) = 0) :
    ‖z-(freeHillValue n:ℂ)-endpointDiagonal r hr hr1 n (q,z)‖ ≤
      endpointCouplingRadius r hr hr1 n q := by
  rw [endpointReducedDeterminant_factorization r hr hr1 n hn q hs z hz] at hd
  have he := congrArg norm (sub_eq_zero.mp hd)
  rw [norm_pow] at he
  have ht := sqrt_endpointCouplingProduct_le_radius r hr hr1 n hn q hs z hz
  rw [← he, Real.sqrt_sq (norm_nonneg _)] at ht
  exact ht

include hn hs in
/-- Lemma 2.11 (23), in squared form, for any two actual determinant zeros.
The roots may coincide; no analytic branch or spectral labeling is assumed. -/
theorem endpointReduced_roots_separation (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (hdz : endpointReducedDeterminant r hr hr1 n (q,z) = 0)
    (hdy : endpointReducedDeterminant r hr hr1 n (q,y) = 0) :
    ‖z-y‖^2 ≤ 6*(endpointCouplingRadius r hr hr1 n q)^2 := by
  have hZ := endpointReduced_root_shift_bound r hr hr1 n hn q hs z hz hdz
  have hY := endpointReduced_root_shift_bound r hr hr1 n hn q hs y hy hdy
  have hdiag := endpointDiagonal_sub_le_eighth r hr hr1 n hn z y hz hy q hs
  have ht : ‖z-y‖ ≤
      ‖endpointDiagonal r hr hr1 n (q,z)-endpointDiagonal r hr hr1 n (q,y)‖ +
      (‖z-(freeHillValue n:ℂ)-endpointDiagonal r hr hr1 n (q,z)‖ +
        ‖y-(freeHillValue n:ℂ)-endpointDiagonal r hr hr1 n (q,y)‖) := by
    calc
      _ = ‖(endpointDiagonal r hr hr1 n (q,z)-endpointDiagonal r hr hr1 n (q,y)) +
        ((z-(freeHillValue n:ℂ)-endpointDiagonal r hr hr1 n (q,z)) -
          (y-(freeHillValue n:ℂ)-endpointDiagonal r hr hr1 n (q,y)))‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
  have hlin : ‖z-y‖ ≤ (16/7:ℝ)*endpointCouplingRadius r hr hr1 n q := by linarith
  have hsq := mul_self_le_mul_self (norm_nonneg (z-y)) hlin
  nlinarith [sq_nonneg (endpointCouplingRadius r hr hr1 n q)]

include hn hs in
/-- The literal square-root form of the root-separation estimate (23). -/
theorem endpointReduced_roots_separation_sqrt (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (hdz : endpointReducedDeterminant r hr hr1 n (q,z) = 0)
    (hdy : endpointReducedDeterminant r hr hr1 n (q,y) = 0) :
    ‖z-y‖ ≤ Real.sqrt 6 * endpointCouplingRadius r hr hr1 n q := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (endpointCouplingRadius_nonneg r hr hr1 n hn q hs))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)]
  exact endpointReduced_roots_separation r hr hr1 n hn q hs z y hz hy hdz hdy

end NLS.KdV
