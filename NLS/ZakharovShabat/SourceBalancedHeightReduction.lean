import NLS.ZakharovShabat.PeriodicDiagonalSimilarity
import NLS.ZakharovShabat.ComponentProductResolvent
import NLS.ZakharovShabat.SourcePrintedHeightCounting

/-! # Reduction of the printed source height to balanced components

Constant diagonal similarity balances any potential with two nonzero
components without increasing the original p-energy norm. Thus the
unrestricted printed height is equivalent to its equal-component-norm
case. This is a reduction, not a proof of that remaining case.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reciprocal rescaling in the source's original p-energy pair space. -/
def sourceDiagonalPotential (c : ℂˣ) : CoeffPair p ≃L[ℂ] CoeffPair p :=
  ((CoeffPair.toMax p).trans (diagonalPotential c)).trans (CoeffPair.toMax p).symm

@[simp] theorem sourceDiagonalPotential_fst (c : ℂˣ) (φ : CoeffPair p) :
    (sourceDiagonalPotential c φ).fst = (c : ℂ) • φ.fst := rfl

@[simp] theorem sourceDiagonalPotential_snd (c : ℂˣ) (φ : CoeffPair p) :
    (sourceDiagonalPotential c φ).snd = (↑c⁻¹ : ℂ) • φ.snd := rfl

/-- Period doubling intertwines the exact source and operator rescalings. -/
theorem periodOnePotential_sourceDiagonalPotential (c : ℂˣ) (φ : CoeffPair p) :
    periodOnePotential (sourceDiagonalPotential c φ) = diagonalPotential c (periodOnePotential φ) := by
  simp only [periodOnePotential_apply, sourceDiagonalPotential_fst,
    sourceDiagonalPotential_snd, map_smul, diagonalPotential_apply]

/-- The entire original source periodic spectrum is unchanged. -/
theorem sourcePeriodicSpectrum_diagonalPotential (hp : p ≠ ⊤) (c : ℂˣ) (φ : CoeffPair p) :
    periodicSpectrum hp (periodOnePotential (sourceDiagonalPotential c φ)) =
      periodicSpectrum hp (periodOnePotential φ) := by
  rw [periodOnePotential_sourceDiagonalPotential, periodicSpectrum_diagonalPotential]

/-- Algebraic multiplicities are preserved in the source convention as well. -/
theorem sourcePeriodicAlgebraicMultiplicity_diagonalPotential (hp : p ≠ ⊤)
    (c : ℂˣ) (φ : CoeffPair p) (z : ℂ) :
    periodicAlgebraicMultiplicity hp (periodOnePotential (sourceDiagonalPotential c φ)) z =
      periodicAlgebraicMultiplicity hp (periodOnePotential φ) z := by
  rw [periodOnePotential_sourceDiagonalPotential, periodicAlgebraicMultiplicity_diagonalPotential]

/-- The energy of equal geometric means does not exceed the original two-component energy. -/
theorem two_mul_geometricMean_rpow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (q : ℝ) :
    2 * (Real.sqrt (a*b))^q ≤ a^q+b^q := by
  have hpow (x : ℝ) (hx : 0 ≤ x) : (x^(q/2))^2 = x^q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    norm_num
  have hg : (Real.sqrt (a*b))^q = a^(q/2)*b^(q/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_nonneg ha hb)]
    convert (Real.mul_rpow ha hb : (a*b)^(q/2) = a^(q/2)*b^(q/2)) using 1
    congr 1
    ring
  rw [hg]
  nlinarith [sq_nonneg (a^(q/2)-b^(q/2)), hpow a ha, hpow b hb]

/-- Equal component norms determine the original source norm exactly. -/
theorem norm_source_eq_of_component_norms (hp : p ≠ ⊤) (φ : CoeffPair p)
    {G : ℝ} (hG : 0 ≤ G) (hfst : ‖φ.fst‖ = G) (hsnd : ‖φ.snd‖ = G) :
    ‖φ‖ = (2 : ℝ)^(1/p.toReal)*G := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne' hp
  rw [WithLp.prod_norm_eq_add hp0, hfst, hsnd, ← two_mul,
    Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hG,
    mul_one_div_cancel hp0.ne', Real.rpow_one]

/-- A balanced source has no larger p-energy norm when its two norms are the original geometric mean. -/
theorem norm_source_le_of_balanced_component_norms (hp : p ≠ ⊤) (φ ψ : CoeffPair p)
    (hfst : ‖ψ.fst‖ = Real.sqrt (‖φ.fst‖*‖φ.snd‖))
    (hsnd : ‖ψ.snd‖ = Real.sqrt (‖φ.fst‖*‖φ.snd‖)) : ‖ψ‖ ≤ ‖φ‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne' hp
  apply (Real.rpow_le_rpow_iff (norm_nonneg ψ) (norm_nonneg φ) hp0).mp
  rw [norm_withLp_prod_rpow hp, norm_withLp_prod_rpow hp, hfst, hsnd, ← two_mul]
  exact two_mul_geometricMean_rpow_le (norm_nonneg _) (norm_nonneg _) _

/-- Two nonzero source components can be balanced by an actual diagonal similarity,
with the exact resulting norm and a nonincrease in the original source norm. -/
theorem exists_source_balanced_diagonalPotential (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hfst : φ.fst ≠ 0) (hsnd : φ.snd ≠ 0) :
    ∃ c : ℂˣ,
      ‖(sourceDiagonalPotential c φ).fst‖ = Real.sqrt (‖φ.fst‖*‖φ.snd‖) ∧
      ‖(sourceDiagonalPotential c φ).snd‖ = Real.sqrt (‖φ.fst‖*‖φ.snd‖) ∧
      ‖sourceDiagonalPotential c φ‖ =
        (2 : ℝ)^(1/p.toReal)*Real.sqrt (‖φ.fst‖*‖φ.snd‖) ∧
      ‖sourceDiagonalPotential c φ‖ ≤ ‖φ‖ := by
  let G := Real.sqrt (‖φ.fst‖*‖φ.snd‖)
  have ha : 0 < ‖φ.fst‖ := norm_pos_iff.mpr hfst
  have hb : 0 < ‖φ.snd‖ := norm_pos_iff.mpr hsnd
  have hG : 0 < G := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hGs : G^2 = ‖φ.fst‖*‖φ.snd‖ := Real.sq_sqrt (by positivity)
  let r : ℝ := G/‖φ.fst‖
  have hr : 0 < r := div_pos hG ha
  let c : ℂˣ := Units.mk0 (r : ℂ) (by exact_mod_cast hr.ne')
  have hcnorm : ‖(c : ℂ)‖ = r := by
    change ‖(r : ℂ)‖ = r
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have h₁ : ‖(sourceDiagonalPotential c φ).fst‖ = G := by
    rw [sourceDiagonalPotential_fst, norm_smul, hcnorm]
    exact div_mul_cancel₀ G ha.ne'
  have h₂ : ‖(sourceDiagonalPotential c φ).snd‖ = G := by
    rw [sourceDiagonalPotential_snd, norm_smul, Units.val_inv_eq_inv_val, norm_inv, hcnorm]
    change (G/‖φ.fst‖)⁻¹*‖φ.snd‖ = G
    rw [inv_div, div_mul_eq_mul_div]
    apply (div_eq_iff hG.ne').mpr
    nlinarith [hGs]
  exact ⟨c,h₁,h₂,norm_source_eq_of_component_norms hp _ hG.le h₁ h₂,
    norm_source_le_of_balanced_component_norms hp φ _ h₁ h₂⟩

/-- Proving the printed height for equal component norms suffices for every source.
Triangular cases are handled by the existing component-product criterion. -/
theorem source_printedHeight_of_balanced (hp : p ≠ ⊤)
    (hbalanced : ∀ ψ : CoeffPair p, ‖ψ.fst‖ = ‖ψ.snd‖ → ∀ z : ℂ,
      z ∈ periodicSpectrum hp (periodOnePotential ψ) → |z.im| < (1+8*‖ψ‖)^p.toReal)
    (φ : CoeffPair p) {z : ℂ} (hz : z ∈ periodicSpectrum hp (periodOnePotential φ)) :
    |z.im| < (1+8*‖φ‖)^p.toReal := by
  by_cases hfst : φ.fst = 0
  · apply sourceSpectrum_abs_im_lt_printed_height_component_product hp φ _ hz
    simp [hfst]
  by_cases hsnd : φ.snd = 0
  · apply sourceSpectrum_abs_im_lt_printed_height_component_product hp φ _ hz
    simp [hsnd]
  obtain ⟨c,h₁,h₂,_,hn⟩ := exists_source_balanced_diagonalPotential hp φ hfst hsnd
  have hspec : z ∈ periodicSpectrum hp (periodOnePotential (sourceDiagonalPotential c φ)) := by
    rwa [sourcePeriodicSpectrum_diagonalPotential]
  exact (hbalanced _ (h₁.trans h₂.symm) z hspec).trans_le
    (Real.rpow_le_rpow (by positivity) (by linarith) ENNReal.toReal_nonneg)

/-- The reduction is exact at each exponent; it does not strengthen the required height. -/
theorem source_printedHeight_iff_balanced (hp : p ≠ ⊤) :
    (∀ φ : CoeffPair p, ∀ z : ℂ, z ∈ periodicSpectrum hp (periodOnePotential φ) →
      |z.im| < (1+8*‖φ‖)^p.toReal) ↔
    (∀ φ : CoeffPair p, ‖φ.fst‖ = ‖φ.snd‖ → ∀ z : ℂ,
      z ∈ periodicSpectrum hp (periodOnePotential φ) → |z.im| < (1+8*‖φ‖)^p.toReal) :=
  ⟨fun h φ _ => h φ, fun h φ _z hz => source_printedHeight_of_balanced hp h φ hz⟩

/-- Any violation transfers to an equal-component-norm source at the same spectral
parameter, with no increase in the original norm. This does not assert a violation exists. -/
theorem source_printedHeight_counterexample_balances (hp : p ≠ ⊤) (φ : CoeffPair p)
    {z : ℂ} (hz : z ∈ periodicSpectrum hp (periodOnePotential φ))
    (hbad : (1+8*‖φ‖)^p.toReal ≤ |z.im|) :
    ∃ ψ : CoeffPair p, ‖ψ.fst‖ = ‖ψ.snd‖ ∧ ‖ψ‖ ≤ ‖φ‖ ∧
      z ∈ periodicSpectrum hp (periodOnePotential ψ) ∧
      (1+8*‖ψ‖)^p.toReal ≤ |z.im| := by
  have hfst : φ.fst ≠ 0 := by
    intro h
    exact (not_lt_of_ge hbad) (sourceSpectrum_abs_im_lt_printed_height_component_product hp φ
      (by simp [h]) hz)
  have hsnd : φ.snd ≠ 0 := by
    intro h
    exact (not_lt_of_ge hbad) (sourceSpectrum_abs_im_lt_printed_height_component_product hp φ
      (by simp [h]) hz)
  obtain ⟨c,h₁,h₂,_,hn⟩ := exists_source_balanced_diagonalPotential hp φ hfst hsnd
  refine ⟨sourceDiagonalPotential c φ,h₁.trans h₂.symm,hn,?_,?_⟩
  · rwa [sourcePeriodicSpectrum_diagonalPotential]
  · exact (Real.rpow_le_rpow (by positivity) (by linarith) ENNReal.toReal_nonneg).trans hbad

/-- A balanced-case height proof supplies the full original counting statement,
on one common neighborhood and at every sufficiently large cutoff. -/
theorem exists_source_periodicCounting_printed_height_of_balanced (hp : p ≠ ⊤)
    (hbalanced : ∀ ψ : CoeffPair p, ‖ψ.fst‖ = ‖ψ.snd‖ → ∀ z : ℂ,
      z ∈ periodicSpectrum hp (periodOnePotential ψ) → |z.im| < (1+8*‖ψ‖)^p.toReal)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ V : Set (CoeffPair p), 0 < N₀ ∧ IsOpen V ∧ Convex ℝ V ∧ φ ∈ V ∧ 0 ∈ V ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => heightRectangleIntegral hp (periodOnePotential ψ) N
          ((1+8*‖ψ‖)^p.toReal)) V ∧
        ∀ ψ ∈ V, PeriodicCountingData hp (periodOnePotential ψ) N ∧
          heightPeriodicSpectrum hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal) =
            centralPeriodicSpectrum hp (periodOnePotential ψ) N ∧
          (∑ z ∈ heightPeriodicSpectrum hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal),
            periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z) = 4*N+2 ∧
          heightRectangleIntegral hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal) =
            centralSpectralProjection hp (periodOnePotential ψ) N ∧
          periodicSpectrum hp (periodOnePotential ψ) ⊆
            heightSpectralBox N ((1+8*‖ψ‖)^p.toReal) ∪ highSpectralDisks N (Real.pi/4) := by
  apply exists_source_periodicCounting_printed_height_of_resolvent hp _ φ
  intro ψ z hz
  by_contra h
  exact (not_lt_of_ge hz) (source_printedHeight_of_balanced hp hbalanced ψ h)

end NLS.ZakharovShabat

