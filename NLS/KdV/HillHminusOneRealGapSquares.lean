import NLS.KdV.HillHminusOneGapQuotientAsymptotics
import NLS.KdV.HillHminusOnePhysicalCut
import NLS.ComplexAnalysis.NearImaginarySquare
import NLS.ComplexAnalysis.QuadraticRootContourPeriod

/-! # Nonnegative filled squares along actual real H^-1 high gaps

The unit root is close to +i/(2*n*pi), so its square has negative real
part. The real endpoint factor reverses this sign on the gap. Reality
of the filled square follows from the actual physical half-plane sheets.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_nonnegative_high_gap_squares (q : PeriodOneHminusOne) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧ ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
          K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        ∀ a ∈ V, IsRealPeriodOneHminusOne a → ∃ l u : ℝ, ∃ B : ℂ → ℂ,
          l ≤ u ∧ HillHminusHighGapPair a n r (l : ℂ) (u : ℂ) ∧
          (l : ℂ) ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/32) ∧
          (u : ℂ) ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/32) ∧
          AnalyticOnNhd ℂ B
            (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \
              segment ℝ (l : ℂ) (u : ℂ)) ∧
          (∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \
              segment ℝ (l : ℂ) (u : ℂ), B z ≠ 0 ∧ B z^2 = K (z,a)) ∧
          ∀ x ∈ Icc l u, (K ((x : ℂ),a)).im = 0 ∧ 0 ≤ (K ((x : ℂ),a)).re := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_near_free_gap_units q
  obtain ⟨N,V,hN,hV,hq,hdata⟩ := hfamily (1/4) (by norm_num) (by norm_num)
  refine ⟨r,hr,hrpi,N,V,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,_,hmatch,hpairs⟩ := hdata n hn
  refine ⟨K,hK,hmatch,?_⟩
  intro a ha hreal
  obtain ⟨l,u,H,hpair,hl,hu,hH,hunit⟩ := hpairs a ha
  obtain ⟨hli,hui⟩ := HillHminusHighGapPair.im_eq_zero hreal hpair
  have hel : (l.re : ℂ) = l := by apply Complex.ext <;> simp [hli]
  have heu : (u.re : ℂ) = u := by apply Complex.ext <;> simp [hui]
  let L : ℝ := min l.re u.re
  let U : ℝ := max l.re u.re
  let c : ℝ := Real.pi*(n : ℕ)
  let E : ℂ := (c : ℂ)^2
  let R : ℝ := c*r
  have hc : 0 < c := by dsimp only [c]; positivity
  have hR : 0 < R := mul_pos hc hr
  have hcenter : ((Real.pi : ℂ)*(n : ℕ))^2 = E := by simp only [E,c,ofReal_mul,ofReal_natCast]
  have hdisc : hillHminusGapSquareDisc n r = closedBall E R := by
    simp only [hillHminusGapSquareDisc,classicalHillGapSquareDisc,hcenter,R,c]
  have hl' : l ∈ ball E (R/32) := by
    apply ball_subset_ball (by change (1/4/64)*R ≤ R/32; linarith : (1/4/64)*(Real.pi*(n : ℕ)*r) ≤ R/32)
    simpa only [hcenter] using hl
  have hu' : u ∈ ball E (R/32) := by
    apply ball_subset_ball (by change (1/4/64)*R ≤ R/32; linarith : (1/4/64)*(Real.pi*(n : ℕ)*r) ≤ R/32)
    simpa only [hcenter] using hu
  have hLU : L ≤ U := min_le_max
  have hordered : HillHminusHighGapPair a n r (L : ℂ) (U : ℂ) := by
    rcases le_total l.re u.re with h | h
    · simpa only [L,U,min_eq_left h,max_eq_right h,hel,heu] using hpair
    · simpa only [L,U,min_eq_right h,max_eq_left h,hel,heu] using hpair.swap
  have hL : (L : ℂ) ∈ ball E (R/32) := by
    rcases le_total l.re u.re with h | h
    · simpa only [L,min_eq_left h,hel] using hl'
    · simpa only [L,min_eq_right h,heu] using hu'
  have hU : (U : ℂ) ∈ ball E (R/32) := by
    rcases le_total l.re u.re with h | h
    · simpa only [U,max_eq_right h,heu] using hu'
    · simpa only [U,max_eq_left h,hel] using hl'
  have hfactor (z : ℂ) (hz : z ∈ closedBall E R) :
      K (z,a) = (z-(L : ℂ))*(z-(U : ℂ))*H z^2 := by
    have he := (hunit z (hdisc ▸ hz)).2.2.1
    rcases le_total l.re u.re with h | h
    · simpa only [L,U,min_eq_left h,max_eq_right h,hel,heu] using he
    · simpa only [L,U,min_eq_right h,max_eq_left h,hel,heu,mul_comm (z-u) (z-l)] using he
  let B : ℂ → ℂ := fun z => endpointRoot (L : ℂ) (U : ℂ) z*H z
  have hB : AnalyticOnNhd ℂ B (ball E R \ segment ℝ (L : ℂ) (U : ℂ)) := by
    intro z hz
    exact (analyticOnNhd_endpointRoot (L : ℂ) (U : ℂ) z hz.2).mul
      (hH z (hdisc ▸ ball_subset_closedBall hz.1))
  have hBsq (z : ℂ) (hz : z ∈ ball E R \ segment ℝ (L : ℂ) (U : ℂ)) :
      B z ≠ 0 ∧ B z^2 = K (z,a) := by
    refine ⟨mul_ne_zero (endpointRoot_ne_zero _ _ z hz.2)
      (hunit z (hdisc ▸ ball_subset_closedBall hz.1)).1,?_⟩
    dsimp only [B]
    rw [mul_pow,endpointRoot_sq _ _ z hz.2,← hfactor z (ball_subset_closedBall hz.1)]
  refine ⟨L,U,B,hLU,hordered,?_,?_,?_,?_,?_⟩
  · simpa only [hcenter,R,c] using hL
  · simpa only [hcenter,R,c] using hU
  · simpa only [hcenter,R,c] using hB
  · simpa only [hcenter,R,c] using hBsq
  · intro x hx
    have hxball : (x : ℂ) ∈ ball E R := by
      have hEl : E = ((freeHillValue (n : ℕ) : ℝ) : ℂ) := by
        dsimp only [E,c,freeHillValue]; push_cast; ring
      have hlabs : |L-freeHillValue (n : ℕ)| < R/32 := by
        simpa only [hEl,mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hL
      have huabs : |U-freeHillValue (n : ℕ)| < R/32 := by
        simpa only [hEl,mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hU
      rw [hEl,mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
      apply (show |x-freeHillValue (n : ℕ)| < R/32 from abs_lt.mpr
        ⟨by linarith [(abs_lt.mp hlabs).1,hx.1],by linarith [(abs_lt.mp huabs).2,hx.2]⟩).trans
      linarith
    have hxdisc := hdisc ▸ ball_subset_closedBall hxball
    constructor
    · have hEl : E = ((freeHillValue (n : ℕ) : ℝ) : ℂ) := by
        dsimp only [E,c,freeHillValue]; push_cast; ring
      apply hillHminus_filled_square_real a hreal n (freeHillValue (n : ℕ)) R x (fun z => K (z,a))
      · intro z hz
        exact (hK (z,a) ⟨hdisc ▸ ball_subset_closedBall (hEl ▸ hz),ha⟩).comp
          (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
      · simpa only [hEl] using hxball
      · intro z hz hi
        exact hmatch (z,a) ⟨⟨hdisc ▸ ball_subset_closedBall (hEl ▸ hz),ha⟩,
          mem_hillHminusContinuationDomain_of_im_ne_zero a hreal z hi⟩
    · apply re_two_endpoint_square_nonneg (fun z => K (z,a)) H L U x hx (hfactor _ (ball_subset_closedBall hxball))
      have ht : 0 < 1/(2*c) := by positivity
      apply (re_sq_neg_of_near_imaginary (H (x : ℂ)) (1/(2*c)) ht ?_).le
      have he : I/(2*(c : ℂ)) = I*((1/(2*c) : ℝ) : ℂ) := by push_cast; ring
      rw [← he]
      have hh := (hunit (x : ℂ) hxdisc).2.2.2
      have hh' : ‖H (x : ℂ)-I/(2*(c : ℂ))‖ ≤ (1/4 : ℝ)/(2*c) := by
        simpa only [c,ofReal_mul,ofReal_natCast,mul_assoc] using hh
      exact hh'.trans_eq (by ring)

end NLS.KdV
