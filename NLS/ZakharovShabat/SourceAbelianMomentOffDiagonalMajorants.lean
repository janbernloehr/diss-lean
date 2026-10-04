import NLS.ZakharovShabat.SourceAbelianMomentSquaredOffsetError
import NLS.ZakharovShabat.SourceAbelianMomentSquareMajorants
import NLS.ZakharovShabat.SourcePsiRefinedActualGapMajorants
import NLS.SequenceSpaces.RefinedProductMajorant

/-! # Uniform refined rows for off-diagonal second moments

The actual squared-gap root offsets, square errors, and chi errors give
an all-index cubic-gap bound. Hölder multiplication of the gap and offset
sequences supplies the leading term at the refined exponent. Pointwise
norm bounds absorb the products of error sequences with uniform constants.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem cubic_error_coefficient_le (x h e f X F : ℝ)
    (hx : 0 ≤ x) (he : 0 ≤ e) (hf : 0 ≤ f) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (hxh : x ≤ h) (hxX : x ≤ X) (hfF : f ≤ F) :
    x/4+2*(x+1/2)*(e*(f+1)+f/4) ≤ h+2*(X+1)*(F+1)*(e+f) := by
  have herror : e*(f+1)+f/4 ≤ (F+1)*(e+f) := by
    nlinarith [mul_nonneg he (sub_nonneg.mpr hfF),mul_nonneg hF hf]
  have hprod := mul_le_mul (show 2*(x+1/2) ≤ 2*(X+1) by linarith) herror
    (by positivity : 0 ≤ e*(f+1)+f/4) (by positivity : 0 ≤ 2*(X+1))
  nlinarith

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {A : SourceAbelianMomentAtlas hp hp1 W s}

/-- The actual second moments have a cubic-gap majorant in every finite
refined exponent. Its norm is locally uniform in the source and uniform
in the deleted index; collapsed gaps are included without division. -/
theorem SourceAbelianMomentErrorDomain.exists_local_offDiagonal_secondMoment_majorants
    (D : SourceAbelianMomentErrorDomain A)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (hφV : φ.val ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ D.domain ∩ V ∧
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∃ B : Coeff r, ‖B‖ ≤ M ∧
          ∀ k : ℤ, k ≠ n → ‖((n-k:ℤ):ℂ)*A.moment n k 2 ψ‖ ≤
            ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^3*‖B k‖ := by
  obtain ⟨Ts,hTs,hφs,_,hsquare⟩ := A.exists_local_refined_square_gap_majorants φ
  obtain ⟨Tf,hTf,hφf,hfV,hfactor⟩ := hs.exists_local_refined_actualGap_majorants φ hφV
  obtain ⟨Ta,hTa,hφa,_,C,hC,hoffset⟩ := hs.locally_uniform_squared_gap_offsets φ.val hφV
  obtain ⟨_,_,Tg,hTg,hφg,R,hR,hgap⟩ := exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ.val
    (by norm_num : (0:ℝ) < 1)
  let T := (Ts ∩ Tf) ∩ ((Ta ∩ Tg) ∩ D.domain)
  refine ⟨T,(hTs.inter hTf).inter ((hTa.inter hTg).inter D.isOpen_domain),
    ⟨⟨hφs,hφf⟩,⟨hφa,hφg⟩,D.real_subset φ.property⟩,
    fun ψ hψ => ⟨hψ.2.2,hfV hψ.1.2⟩,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  have hr0 := (zero_lt_one.trans hr1).ne'
  obtain ⟨Ms,hMs,hsrows⟩ := hsquare r hr hr1 hpr
  obtain ⟨Mf,hMf,hfrows⟩ := hfactor r hr hr1 hpr
  let X := R*C
  have hX : 0 ≤ X := mul_nonneg hR hC.le
  let L := 2*(X+1)*(Mf+1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨X+L*(Ms+Mf),by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨E,hE,hS⟩ := hsrows ψ hψ.1.1
  obtain ⟨F,hF,_,hchi⟩ := hfrows ψ hψ.1.2 n
  obtain ⟨α,_,hα,hαnorm⟩ := hoffset ψ hψ.2.1.1 n
  obtain ⟨H,hH,hHnorm⟩ := Coeff.exists_refined_product_majorant hp (zero_lt_one.trans hp1)
    hr (zero_lt_one.trans hr1) hpr (sourcePeriodicGapDisplacement hp hp1 ψ) α
  have hHX : ‖H‖ ≤ X := hHnorm.trans (mul_le_mul (hgap ψ hψ.2.1.2).1 hαnorm (norm_nonneg _) hR)
  let B := Coeff.magnitude H+(L:ℂ) • (Coeff.magnitude E+Coeff.magnitude F)
  have hBpoint (k : ℤ) : ‖B k‖ = ‖H k‖+L*(‖E k‖+‖F k‖) := by
    simp only [B,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      Coeff.magnitude_apply,← Complex.ofReal_add,← Complex.ofReal_mul,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  have hBnorm : ‖B‖ ≤ X+L*(Ms+Mf) := by
    have hEF : ‖Coeff.magnitude E+Coeff.magnitude F‖ ≤ Ms+Mf :=
      (norm_add_le _ _).trans (by simpa only [Coeff.norm_magnitude] using add_le_add hE hF)
    calc
      ‖B‖ ≤ ‖Coeff.magnitude H‖+‖(L:ℂ) • (Coeff.magnitude E+Coeff.magnitude F)‖ := norm_add_le _ _
      _ = ‖H‖+L*‖Coeff.magnitude E+Coeff.magnitude F‖ := by
        rw [Coeff.norm_magnitude,norm_smul,Complex.norm_real,Real.norm_of_nonneg hL]
      _ ≤ X+L*(Ms+Mf) := add_le_add hHX (mul_le_mul_of_nonneg_left hEF hL)
  refine ⟨B,hBnorm,?_⟩
  intro k hkn
  have hbound := D.offDiagonal_squaredOffset_bound ψ hψ.2.2 n k hkn (α k) (hα k hkn)
    ‖E k‖ ‖F k‖ (norm_nonneg _) (hS k) (hchi k hkn)
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [hBpoint]
  exact cubic_error_coefficient_le _ _ _ _ X Mf (by positivity) (norm_nonneg _) (norm_nonneg _)
    hX hMf (hH k) ((hH k).trans ((lp.norm_apply_le_norm hr0 H k).trans hHX))
    ((lp.norm_apply_le_norm hr0 F k).trans hF)

end NLS.ZakharovShabat
