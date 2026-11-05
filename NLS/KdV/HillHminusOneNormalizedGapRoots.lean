import NLS.KdV.HillHminusOneNormalizedGapSquares
import NLS.ComplexAnalysis.NormalizedAnalyticSquareRoot

/-! # The normalized analytic high Hill gap root

The root of the actual filled quotient is analytic on the whole disc,
including both spectral endpoints and collapsed gaps. Its exact squared
factorization and locally uniform normalization precede the action estimate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- Principal analytic root of the normalized filled actual gap square. -/
def hillHminusNormalizedGapRoot (n : ℕ+) (K : ℂ × PeriodOneHminusOne → ℂ)
    (a : PeriodOneHminusOne) (l u z : ℂ) : ℂ :=
  Complex.sqrt (hillHminusNormalizedGapSquare n K a l u z)

theorem hillHminusNormalizedGapRoot_sq (n : ℕ+) (K : ℂ × PeriodOneHminusOne → ℂ)
    (a : PeriodOneHminusOne) (l u z : ℂ) :
    hillHminusNormalizedGapRoot n K a l u z^2 =
      hillHminusNormalizedGapSquare n K a l u z :=
  complex_sqrt_sq _

/-- Exact factorization with the original free high-energy normalization. -/
theorem hillHminusNormalizedGapRoot_factor (n : ℕ+) (K : ℂ × PeriodOneHminusOne → ℂ)
    (a : PeriodOneHminusOne) (l u : ℂ)
    (hf : ∀ z : ℂ, K (z,a) = (z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z)
    (z : ℂ) :
    K (z,a) = -(z-l)*(z-u)*hillHminusNormalizedGapRoot n K a l u z^2 /
      (4*((Real.pi : ℂ)*(n : ℕ))^2) := by
  have hc : ((Real.pi : ℂ)*(n : ℕ)) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast n.ne_zero)
  rw [hillHminusNormalizedGapRoot_sq, hf z]
  dsimp [hillHminusNormalizedGapSquare, normalizedQuadraticDeflation]
  push_cast
  field_simp

/-- The analytic, nonvanishing root inherits the filled square's error bound. -/
theorem hillHminusNormalizedGapRoot_analytic_bound
    (n : ℕ+) (r epsilon : ℝ) (hepsilon : epsilon < 1)
    (K : ℂ × PeriodOneHminusOne → ℂ) (a : PeriodOneHminusOne) (l u : ℂ)
    (hQ : AnalyticOnNhd ℂ (hillHminusNormalizedGapSquare n K a l u)
      (hillHminusGapSquareDisc n r))
    (hbound : ∀ z ∈ hillHminusGapSquareDisc n r,
      ‖hillHminusNormalizedGapSquare n K a l u z-1‖ ≤ epsilon) :
    AnalyticOnNhd ℂ (hillHminusNormalizedGapRoot n K a l u)
      (hillHminusGapSquareDisc n r) ∧
    ∀ z ∈ hillHminusGapSquareDisc n r,
      hillHminusNormalizedGapRoot n K a l u z ≠ 0 ∧
      ‖hillHminusNormalizedGapRoot n K a l u z-1‖ ≤ epsilon := by
  refine ⟨analyticOnNhd_principalSqrt_of_norm_sub_one_lt_one _ _ hQ
    (fun z hz => (hbound z hz).trans_lt hepsilon), ?_⟩
  intro z hz
  have hb : ‖hillHminusNormalizedGapRoot n K a l u z-1‖ ≤ epsilon :=
    (norm_principalSqrt_sub_one_le _).trans (hbound z hz)
  refine ⟨?_,hb⟩
  intro he
  rw [he, zero_sub, norm_neg, norm_one] at hb
  linarith

/-- Actual high root normalization on one common neighborhood and cutoff,
uniform throughout every later closed energy disc, including closed gaps. -/
theorem exists_hillHminus_normalized_gap_roots (q : PeriodOneHminusOne) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V, ‖K t‖ < 1) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant t.2 t.1/2) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          K t = 0 ↔ hillHminusRadicand t.2 t.1 = 0) ∧
        (∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
          K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
          AnalyticOnNhd ℂ (hillHminusNormalizedGapRoot n K a l u)
            (hillHminusGapSquareDisc n r) ∧
          (∀ z : ℂ, K (z,a) = -(z-l)*(z-u)*hillHminusNormalizedGapRoot n K a l u z^2 /
            (4*((Real.pi : ℂ)*(n : ℕ))^2)) ∧
          ∀ z ∈ hillHminusGapSquareDisc n r,
            hillHminusNormalizedGapRoot n K a l u z ≠ 0 ∧
            ‖hillHminusNormalizedGapRoot n K a l u z-1‖ ≤ epsilon := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_normalized_gap_squares q
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon
  let eta : ℝ := min (1/2) epsilon
  have heta : 0 < eta := lt_min (by norm_num) hepsilon
  have heta1 : eta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hetaε : eta ≤ epsilon := min_le_right _ _
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ := hfamily eta heta
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch,hpairs⟩ := hfamily n hn
  refine ⟨K,hK,hbound,hrel,hzero,hmatch,?_⟩
  intro a ha
  obtain ⟨l,u,hpair,hQ,hfactor,hnorm⟩ := hpairs a ha
  obtain ⟨hroot,hrootbound⟩ := hillHminusNormalizedGapRoot_analytic_bound n r eta heta1 K a l u hQ hnorm
  exact ⟨l,u,hpair,hroot,hillHminusNormalizedGapRoot_factor n K a l u hfactor,
    fun z hz => ⟨(hrootbound z hz).1, (hrootbound z hz).2.trans hetaε⟩⟩

end NLS.KdV
