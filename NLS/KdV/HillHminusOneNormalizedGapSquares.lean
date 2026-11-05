import NLS.KdV.HillHminusOneHighGapPairs
import NLS.ComplexAnalysis.QuadraticModelDeflation

/-! # The normalized actual H-minus-one gap square

Deflate the actual filled primitive square at both actual spectral roots.
The free normalization is `-4*(pi*n)^2`. The filled quotient is analytic
on the complete energy disc and tends locally uniformly to one, including
at collapsed gaps. The primitive, trace and physical root identities are
retained in the same family; no spectral model is supplied as an input.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- Normalized filled quotient of the actual primitive square by its two roots. -/
def hillHminusNormalizedGapSquare (n : ℕ+) (K : ℂ × PeriodOneHminusOne → ℂ)
    (a : PeriodOneHminusOne) (l u z : ℂ) : ℂ :=
  normalizedQuadraticDeflation (Real.pi*(n : ℕ)) (fun w => K (w,a)) l u z

/-- Quantitative deflation on one actual spectral disc, with repeated roots allowed. -/
theorem hillHminus_normalized_gap_square_bound
    (n : ℕ+) (r δ : ℝ) (hr : 0 < r) (hδ : 0 ≤ δ) (hδ4 : δ ≤ 1/4)
    (V : Set PeriodOneHminusOne) (K : ℂ × PeriodOneHminusOne → ℂ)
    (hK : AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V))
    (hzero : ∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
      K t = 0 ↔ hillHminusRadicand t.2 t.1 = 0)
    (herror : ∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
      ‖K t-classicalHillFreeQuadraticModel n t.1‖ ≤ δ^2*r^2)
    (a : PeriodOneHminusOne) (ha : a ∈ V) (l u : ℂ)
    (hpair : HillHminusHighGapPair a n r l u)
    (hmult : ∀ z ∈ hillHminusGapSquareDisc n r,
      analyticOrderNatAt (fun w => K (w,a)) z = ({l,u} : Multiset ℂ).count z) :
    AnalyticOnNhd ℂ (hillHminusNormalizedGapSquare n K a l u)
      (hillHminusGapSquareDisc n r) ∧
    (∀ z : ℂ, K (z,a) =
      (z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z) ∧
    ∀ z ∈ hillHminusGapSquareDisc n r,
      ‖hillHminusNormalizedGapSquare n K a l u z-1‖ ≤ 24*δ := by
  let c : ℝ := Real.pi*(n : ℕ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hdisc : hillHminusGapSquareDisc n r = closedBall ((c : ℂ)^2) (c*r) := by
    simp [hillHminusGapSquareDisc, classicalHillGapSquareDisc, c]
  have hf : AnalyticOnNhd ℂ (fun z => K (z,a)) (hillHminusGapSquareDisc n r) := by
    intro z hz
    exact (hK (z,a) ⟨hz,ha⟩).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have hl := ball_subset_closedBall hpair.left_mem
  have hu := ball_subset_closedBall hpair.right_mem
  have hfl := (hzero (l,a) ⟨hl,ha⟩).mpr hpair.left_zero
  have hfu := (hzero (u,a) ⟨hu,ha⟩).mpr hpair.right_zero
  have hlu : l = u → deriv (fun z => K (z,a)) l = 0 := by
    intro he
    by_contra hd
    have hs := (hf l hl).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfl hd
    have hs' : analyticOrderNatAt (fun z => K (z,a)) l = 1 := congrArg ENat.toNat hs
    have hm := hmult l hl
    simp [← he] at hm
    omega
  have hQ := analyticOnNhd_twoRootDeflation (fun z => K (z,a)) _ l u hf hl hu
  refine ⟨?_, twoRootDeflation_factor _ l u hfl hfu hlu, ?_⟩
  · exact analyticOnNhd_const.mul hQ
  · intro z hz
    apply norm_normalizedQuadraticDeflation_sub_one_le c r δ hc hr hδ hδ4
      (fun z => K (z,a)) l u (hdisc ▸ hf) (hdisc ▸ hl) (hdisc ▸ hu) hfl hfu hlu
      ?_ z (hdisc ▸ hz)
    intro w hw
    have he := herror (w,a) ⟨hdisc.symm ▸ hw,ha⟩
    simpa [classicalHillFreeQuadraticModel, c] using he

/-- One radius precedes every accuracy. One H-minus-one neighborhood and
cutoff give normalized analytic quotients for all later physical clusters. -/
theorem exists_hillHminus_normalized_gap_squares (q : PeriodOneHminusOne) :
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
          AnalyticOnNhd ℂ (hillHminusNormalizedGapSquare n K a l u)
            (hillHminusGapSquareDisc n r) ∧
          (∀ z : ℂ, K (z,a) =
            (z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z) ∧
          ∀ z ∈ hillHminusGapSquareDisc n r,
            ‖hillHminusNormalizedGapSquare n K a l u z-1‖ ≤ epsilon := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_quadratic_square_pairs q
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon
  let δ : ℝ := min (1/4) (epsilon/24)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ4 : δ ≤ 1/4 := min_le_left _ _
  have hδe : 24*δ ≤ epsilon := by
    have hh : δ ≤ epsilon/24 := min_le_right _ _
    linarith
  have hδsq : δ^2 ≤ 1/16 := by nlinarith
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ := hfamily (δ^2) (sq_pos_of_pos hδ) hδsq
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch,herror,hpairs⟩ := hfamily n hn
  refine ⟨K,hK,hbound,hrel,hzero,hmatch,?_⟩
  intro a ha
  obtain ⟨_,l,u,hpair,hmult⟩ := hpairs a ha
  obtain ⟨hQ,hfactor,hnorm⟩ := hillHminus_normalized_gap_square_bound n r δ hr hδ.le hδ4
    V K hK hzero herror a ha l u hpair hmult
  exact ⟨l,u,hpair,hQ,hfactor,fun z hz => (hnorm z hz).trans hδe⟩

end NLS.KdV
