import NLS.KdV.HillFiniteBandCover
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Actual finite-gap Hill exterior analyticity and contour independence

Finiteness refers to the noncollapsed positive gaps of the intrinsic real
characteristic labels. The actual filled-square domain contains an exterior
of one bounded disc. Every even power of the actual normalized primitive is
analytic there, and all sufficiently large centered circle periods agree.
The lowest cut and every collapsed positive gap are filled by proved results.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ContDiff
namespace NLS.KdV

theorem exists_hillRealLabels_band_upper_gt (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ) :
    ∃ N : ℕ, x < hillRealLabels q hq hr (2*N+1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max (8*‖q‖) (max 2 (x+4*‖q‖)))
  have hcut : 8*‖q‖ ≤ (N : ℝ) := ((le_max_left _ _).trans_lt hN).le
  have hN2r : 2 < (N : ℝ) := (le_max_left 2 _).trans_lt ((le_max_right _ _).trans_lt hN)
  have hN2 : 2 ≤ N := by exact_mod_cast hN2r.le
  obtain ⟨p,hl,_⟩ := hillRealLabels_high_pair q hq hr N hN2 hcut
  have hp := (p.localization q hq N (by omega) hcut).1
  have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hN1 : 1 ≤ (N : ℝ) := by linarith
  have hfree : (N : ℝ) ≤ freeHillValue N := by
    dsimp only [freeHillValue,Int.cast_natCast]
    exact (show (N : ℝ) ≤ (N : ℝ)^2 by nlinarith).trans
      (le_mul_of_one_le_left (sq_nonneg _) hpi)
  have hxN : x+4*‖q‖ < (N : ℝ) :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hN)
  have hxleft : x < p.left := by linarith [(abs_le.mp hp).1]
  refine ⟨N,hxleft.trans_le ?_⟩
  rw [← hl]
  exact monotone_hillRealLabels q hq hr (by omega)

/-- The actual Hill potential has finitely many noncollapsed positive gaps. -/
def HillFiniteGap (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) : Prop :=
  {n : ℕ | 1 ≤ n ∧ hillRealLabels q hq hr (2*n-1) ≠ hillRealLabels q hq hr (2*n)}.Finite

theorem HillFiniteGap.exists_collapsed_tail (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (hfg : HillFiniteGap q hq hr) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n → hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n) := by
  obtain ⟨N,hN⟩ := hfg.bddAbove
  refine ⟨N+1,?_⟩
  intro n hn hn1
  by_contra he
  have hle : n ≤ N := hN ⟨hn1,he⟩
  omega

/-- Only finitely many actual open gaps remain outside the filled square domain, and all of them lie in one bounded disc. -/
theorem HillFiniteGap.exists_exterior_subset_filled_square (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (hfg : HillFiniteGap q hq hr) :
    ∃ R : ℝ, 0 < R ∧ {z : ℂ | R < ‖z‖} ⊆ hillL2FilledSquareDomain q hq hr := by
  obtain ⟨N,hN⟩ := HillFiniteGap.exists_collapsed_tail q hq hr hfg
  let R := |hillLowestEnergy q hq hr|+|hillRealLabels q hq hr (2*N)|+1
  refine ⟨R,by dsimp only [R];positivity,?_⟩
  intro z hz
  change R < ‖z‖ at hz
  by_cases hi : z.im ≠ 0
  · exact Or.inl (Or.inl hi)
  by_cases hg : z.re ≤ hillLowestEnergy q hq hr
  · exact Or.inr (Or.inl hg)
  have hx0 : hillLowestEnergy q hq hr < z.re := lt_of_not_ge hg
  have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
  have hxR : R < z.re := by
    by_contra hh
    have hlo : -R ≤ z.re := by
      dsimp only [R]
      linarith [neg_abs_le (hillLowestEnergy q hq hr),abs_nonneg (hillRealLabels q hq hr (2*N))]
    have ha := abs_le.mpr ⟨hlo,not_lt.mp hh⟩
    have hnorm : ‖z‖ = |z.re| := by
      conv_lhs => rw [hzC,Complex.norm_real,Real.norm_eq_abs]
    exact (not_lt_of_ge ha) (by simpa only [hnorm] using hz)
  by_cases hgap : ∃ n : ℕ, 1 ≤ n ∧ z.re ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))
  · obtain ⟨n,hn,hx⟩ := hgap
    by_cases hnN : N ≤ n
    · have hc := hN n hnN hn
      refine Or.inr (Or.inr ⟨n,hn,hc,?_⟩)
      linarith [hx.1,hx.2]
    · have hle : hillRealLabels q hq hr (2*n) ≤ hillRealLabels q hq hr (2*N) :=
        monotone_hillRealLabels q hq hr (by omega)
      dsimp only [R] at hxR
      linarith [hx.2,le_abs_self (hillRealLabels q hq hr (2*N)),abs_nonneg (hillLowestEnergy q hq hr)]
  · obtain ⟨M,hM⟩ := exists_hillRealLabels_band_upper_gt q hq hr z.re
    obtain ⟨k,_,hband⟩ := hillRealLabels_finite_band_cover q hq hr M z.re hx0 hM
      (fun n hn _ hx => hgap ⟨n,hn,hx⟩)
    exact Or.inl (Or.inr ⟨k,hband⟩)

theorem hillFiniteGap_iff_collapsed_tail (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    HillFiniteGap q hq hr ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n →
      hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n) := by
  refine ⟨HillFiniteGap.exists_collapsed_tail q hq hr,?_⟩
  rintro ⟨N,hN⟩
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  by_contra he
  exact hn.2 (hN n (not_lt.mp he) hn.1)

/-- One exterior radius precedes every even power and both contour radii. No analytic extension or contour identity is supplied as an assumption. -/
theorem HillFiniteGap.exists_analytic_even_exterior_and_periods (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (hfg : HillFiniteGap q hq hr) :
    ∃ R : ℝ, 0 < R ∧
      (∀ m : ℕ, AnalyticOnNhd ℂ (fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ (2*m))
        {z : ℂ | R < ‖z‖}) ∧
      ∀ m : ℕ, ∀ r : ℝ, R < r → ∀ s : ℝ, R < s →
        (∮ z in C((0 : ℂ),r), hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ (2*m)) =
          ∮ z in C((0 : ℂ),s), hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ (2*m) := by
  obtain ⟨R,hR,hsub⟩ := HillFiniteGap.exists_exterior_subset_filled_square q hq hr hfg
  have ha (m : ℕ) : AnalyticOnNhd ℂ
      (fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ (2*m)) {z : ℂ | R < ‖z‖} := by
    have h0 : AnalyticOnNhd ℂ (fun z => hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) 0 z ^ m)
        {z : ℂ | R < ‖z‖} := ((analyticOnNhd_hillL2FilledSquare q hq hr).mono hsub).pow m
    simpa only [hillL2RealGapPrimitiveSquare,Nat.cast_zero,mul_zero,zero_mul,add_zero,← pow_mul] using! h0
  have hi (m : ℕ) (r s : ℝ) (hrR : R < r) (hrs : r ≤ s) :
      (∮ z in C((0 : ℂ),s), hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ (2*m)) =
        ∮ z in C((0 : ℂ),r), hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ (2*m) := by
    have hA : AnalyticOnNhd ℂ
        (fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ (2*m))
        (closedBall 0 s \ ball 0 r) := (ha m).mono (by
      intro z hz
      have hzR : r ≤ ‖z‖ := by
        by_contra he
        exact hz.2 (mem_ball_zero_iff.mpr (lt_of_not_ge he))
      exact hrR.trans_le hzR)
    exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (hR.trans hrR) hrs countable_empty hA.continuousOn
      (fun z hz => (hA z ⟨ball_subset_closedBall hz.1.1,
        fun h => hz.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
  refine ⟨R,hR,ha,?_⟩
  intro m r hrR s hsR
  by_cases hrs : r ≤ s
  · exact (hi m r s hrR hrs).symm
  · exact hi m s r hsR (le_of_not_ge hrs)

end NLS.KdV
