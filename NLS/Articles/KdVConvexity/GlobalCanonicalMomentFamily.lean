import NLS.Articles.KdVConvexity.CommonCanonicalMomentFamily
import NLS.SequenceSpaces.PeriodOneHminusOneRealForm

/-! # Global potential-space analytic canonical moment families

Real-form uniqueness glues the common local families on one complex
neighborhood of the entire real H^-1 space. The same domain carries every
polynomial and cubic period, with exact real canonical values and locally
uniform complex tail bounds. Birkhoff-action descent remains separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- One complex neighborhood of all real H^-1 potentials carries every
actual canonical moment, with locally uniform quadratic high bounds. -/
theorem exists_global_analytic_canonical_moment_family :
    ∃ Ω : Set PeriodOneHminusOne, IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q} ⊆ Ω ∧
      ∃ A : ℕ+ → ℕ → PeriodOneHminusOne → ℂ, ∃ R : ℕ+ → PeriodOneHminusOne → ℂ,
        (∀ n m, AnalyticOnNhd ℂ (A n m) Ω) ∧ (∀ n, AnalyticOnNhd ℂ (R n) Ω) ∧
        (∀ q : PeriodOneHminusOne, ∀ hq : IsRealPeriodOneHminusOne q, ∀ n : ℕ+,
          (∀ m, A n m q = hillHminusRealGapContourMoment q hq n m) ∧
          R n q = hillHminusRealGapCubicContourMoment q hq n ∧
          0 ≤ (A n 0 q).re ∧ (R n q).re ≤ 0 ∧ (R n q).im = 0 ∧ (R n q = 0 ↔ A n 0 q = 0)) ∧
        ∀ q : PeriodOneHminusOne, IsRealPeriodOneHminusOne q →
          ∃ C : ℝ, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
            0 < C ∧ 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ Ω ∧
            ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ p ∈ V,
              (∀ m, A n m p = hillHminusHighContourMoment (n : ℕ) m p) ∧
              R n p = hillHminusHighCubicContourMoment (n : ℕ) p ∧
              ‖((8*(n : ℕ)*Real.pi : ℝ) : ℂ)*R n p‖ ≤ C*‖A n 0 p‖^2 := by
  classical
  choose C N W hC hN hW hqW A R hAa hRa htail hbound hreal using
    fun q : PeriodOneRealHminusOne => exists_common_analytic_canonical_moment_family q.val q.property
  choose r hr hball using fun q : PeriodOneRealHminusOne =>
    Metric.mem_nhds_iff.mp ((hW q).mem_nhds (hqW q))
  let Ω : Set PeriodOneHminusOne := ⋃ q : PeriodOneRealHminusOne, ball q.val (r q)
  have hAg (n : ℕ+) (m : ℕ) : ∃ G : PeriodOneHminusOne → ℂ,
      AnalyticOnNhd ℂ G Ω ∧ ∀ q : PeriodOneRealHminusOne, EqOn G (A q n m) (ball q.val (r q)) := by
    obtain ⟨G,hG,hlocal,_⟩ := exists_analyticOnNhd_gluing_realHminus
      (fun q : PeriodOneRealHminusOne => q) r (fun q => A q n m)
      (fun q => (hAa q n m).mono (hball q)) (by
        intro i j p hp hpr
        exact ((hreal i p (hball i hp.1) hpr n).1 m).trans
          ((hreal j p (hball j hp.2) hpr n).1 m).symm)
    exact ⟨G,hG,hlocal⟩
  have hRg (n : ℕ+) : ∃ G : PeriodOneHminusOne → ℂ,
      AnalyticOnNhd ℂ G Ω ∧ ∀ q : PeriodOneRealHminusOne, EqOn G (R q n) (ball q.val (r q)) := by
    obtain ⟨G,hG,hlocal,_⟩ := exists_analyticOnNhd_gluing_realHminus
      (fun q : PeriodOneRealHminusOne => q) r (fun q => R q n)
      (fun q => (hRa q n).mono (hball q)) (by
        intro i j p hp hpr
        exact ((hreal i p (hball i hp.1) hpr n).2.1).trans
          ((hreal j p (hball j hp.2) hpr n).2.1).symm)
    exact ⟨G,hG,hlocal⟩
  choose GA hGA hGALocal using hAg
  choose GR hGR hGRLocal using hRg
  have hcanon (p : PeriodOneHminusOne) (hpr : IsRealPeriodOneHminusOne p) (n : ℕ+) :
      (∀ m, GA n m p = hillHminusRealGapContourMoment p hpr n m) ∧
        GR n p = hillHminusRealGapCubicContourMoment p hpr n := by
    let a : PeriodOneRealHminusOne := ⟨p,hpr⟩
    have hp : p ∈ ball a.val (r a) := mem_ball_self (hr a)
    have hloc := hreal a p (hball a hp) hpr n
    exact ⟨fun m => (hGALocal n m a hp).trans (hloc.1 m),(hGRLocal n a hp).trans hloc.2.1⟩
  refine ⟨Ω,isOpen_iUnion (fun _ => isOpen_ball),?_,GA,GR,hGA,hGR,?_,?_⟩
  · intro p hpr
    exact mem_iUnion.mpr ⟨⟨p,hpr⟩,mem_ball_self (hr ⟨p,hpr⟩)⟩
  · intro p hpr n
    obtain ⟨hAm,hRm⟩ := hcanon p hpr n
    refine ⟨hAm,hRm,?_,?_,?_,?_⟩
    · rw [hAm 0]
      simpa only [Nat.mul_zero] using hillHminusRealGapContourMoment_even_nonneg p hpr n 0
    · rw [hRm]
      exact (hillHminusRealGapCubicContourMoment_nonpositive p hpr n).1
    · rw [hRm]
      exact (hillHminusRealGapCubicContourMoment_nonpositive p hpr n).2
    · rw [hRm,hAm 0]
      exact hillHminusRealGapCubicContourMoment_eq_zero_iff_Arnold_zero p hpr n
  · intro p hpr
    let a : PeriodOneRealHminusOne := ⟨p,hpr⟩
    refine ⟨C a,N a,ball a.val (r a),hC a,hN a,isOpen_ball,mem_ball_self (hr a),?_,?_⟩
    · exact fun _ hz => mem_iUnion.mpr ⟨a,hz⟩
    · intro n hn z hz
      refine ⟨fun m => (hGALocal n m a hz).trans ((htail a n hn z).1 m),
        (hGRLocal n a hz).trans (htail a n hn z).2,?_⟩
      rw [hGRLocal n a hz,hGALocal n 0 a hz]
      exact hbound a n hn z (hball a hz)

end NLS.Articles.KdVConvexity
