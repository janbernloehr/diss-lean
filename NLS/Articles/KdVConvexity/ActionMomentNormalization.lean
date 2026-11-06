import NLS.ComplexAnalysis.ScalarFamilyTransport
import NLS.Articles.KdVConvexity.ArnoldConeMomentGerms

/-! # Normalizing the glued actual cubic action family -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

theorem cubicContourScale_ne_zero (n : ℕ+) : cubicContourScale n ≠ 0 := by
  dsimp only [cubicContourScale]
  exact_mod_cast (by positivity : 8*(n : ℝ)*Real.pi ≠ 0)

def unscaledCubicActionFamily (G : ℕ+ → Coeff 1 → ℂ) (n : ℕ+) (b : BaseActionSpace) : ℂ :=
  G n (baseActionNormalization b)/cubicContourScale n

theorem weighted_unscaledCubicActionFamily (G : ℕ+ → Coeff 1 → ℂ) (n : ℕ+) (b : BaseActionSpace) :
    weightedContourTerm (unscaledCubicActionFamily G) n b = G n (baseActionNormalization b) :=
  mul_div_cancel₀ _ (cubicContourScale_ne_zero n)

theorem analyticOnNhd_unscaledCubicActionFamily (G : ℕ+ → Coeff 1 → ℂ)
    (V : Set (Coeff 1)) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V) (n : ℕ+) :
    AnalyticOnNhd ℂ (unscaledCubicActionFamily G n) (baseActionNormalization ⁻¹' V) := by
  exact NLS.ComplexAnalysis.analyticOnNhd_scalarFamily_div_preimage
    baseActionNormalization cubicContourScale G V hG n

theorem tail_bounds_unscaledCubicActionFamily (G : ℕ+ → Coeff 1 → ℂ)
    (V : Set (Coeff 1))
    (hbound : ∀ b ∈ V, ∃ T : Set (Coeff 1), IsOpen T ∧ b ∈ T ∧ T ⊆ V ∧
      ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ T, ∀ n ∉ s,
        ‖G n c‖ ≤ C*‖normalizedRawActionCoordinate n c‖^2) :
    ∀ b ∈ baseActionNormalization ⁻¹' V, ∃ T : Set BaseActionSpace, IsOpen T ∧ b ∈ T ∧
      T ⊆ baseActionNormalization ⁻¹' V ∧ ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧
        ∀ c ∈ T, ∀ n ∉ s, ‖weightedContourTerm (unscaledCubicActionFamily G) n c‖ ≤
          C*‖c.val (actionIndexEquiv.symm n)‖^2 := by
  have hJ (n : ℕ+) (b : BaseActionSpace) : normalizedRawActionCoordinate n (baseActionNormalization b) =
      b.val (actionIndexEquiv.symm n) := by
    unfold normalizedRawActionCoordinate
    rw [baseActionNormalization.symm_apply_apply]
  exact NLS.ComplexAnalysis.scalarFamily_div_tail_bounds_preimage baseActionNormalization
    cubicContourScale cubicContourScale_ne_zero G normalizedRawActionCoordinate
    (fun n b => b.val (actionIndexEquiv.symm n)) hJ V hbound

theorem ArnoldConeSourceFamily.unscaledCubicRecovery
    (I : PeriodOneHminusOne → BaseActionSpace) (S : ArnoldConeSourceFamily I)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (hpos : ∀ q, IsRealPeriodOneHminusOne q → I q ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hGrec : ∀ n a, G n a.val = S.scaledCubicMoment n a)
    (p : PeriodOneHminusOne) (hp : IsRealPeriodOneHminusOne p) (hm : p.val 0 = 0) (n : ℕ+) :
    unscaledCubicActionFamily G n (I p) = hillHminusRealGapCubicContourMoment p hp n := by
  let a : Coeff.nonnegativeLocus 1 :=
    ⟨baseActionNormalization (I p),
      (WeightedCoeff.mem_nonnegativeLocus_iff baseActionWeight 1 (I p)).mp (hpos p hp)⟩
  have heI : I (S.potential a) = I p := by
    rw [S.action a]
    exact baseActionNormalization.symm_apply_apply _
  have heD := hillHminusDiscriminant_eq_of_global_Arnold_eq I hrec
    (S.potential a) p (S.real a) hp (S.meanZero a) hm heI
  have heM := (hillHminusRealGapContourMoments_eq_of_discriminant_eq
    (S.potential a) p (S.real a) hp heD n).2
  change G n a.val/cubicContourScale n = _
  rw [hGrec n a]
  change (cubicContourScale n*hillHminusRealGapCubicContourMoment (S.potential a) (S.real a) n)/
    cubicContourScale n = _
  rw [mul_div_cancel_left₀ _ (cubicContourScale_ne_zero n),heM]

end NLS.Articles.KdVConvexity
