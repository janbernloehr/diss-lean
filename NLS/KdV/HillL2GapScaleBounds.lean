import NLS.KdV.HillL2GapQuotients
import NLS.KdV.ClassicalHillGapScaleBounds

/-! # Actual L2 primitive bounds on the gap-length scale

The endpoint quotient gives a square bound on the whole gap-sized disc
and an actual shifted primitive bound wherever source continuation is
admissible. The neighborhood is open in the complex L2 norm.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- The cutoff, complex neighborhood and constant precede all high
indices and all actual gap pairs. The square estimate holds throughout
the full gap-sized disc, including collapsed gaps and nonadmissible
energies; the continued primitive estimate holds wherever it is defined. -/
theorem exists_hillL2_gap_scaled_primitive_bounds (q : Coeff 2) :
    ∃ r C : ℝ, ∃ N : ℕ, ∃ V : Set (Coeff 2),
      0 < r ∧ 0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ K (hillL2GapSquareDisc n r ×ˢ V) ∧
        ∀ a ∈ V, ∃ l u : ℂ, HillL2HighGapPair a n l u ∧
          (closedBall ((l+u)/2) ‖l-u‖ ⊆ hillL2GapSquareDisc n r) ∧
          (∀ z ∈ closedBall ((l+u)/2) ‖l-u‖,
            ‖K (z,a)‖ ≤ 9*‖l-u‖^2/(Real.pi*(n : ℕ)*r)^2) ∧
          ∀ z ∈ closedBall ((l+u)/2) ‖l-u‖,
            (z,a) ∈ hillL2ContinuationDomain →
              ‖hillL2ContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi‖ ≤ C*‖l-u‖/(n : ℕ) := by
  obtain ⟨r,N,V,hr,_,hN,hV,hq,hfamily⟩ := exists_hillL2_gap_quotient_bounds q
  let C : ℝ := 3/(Real.pi*r)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨r,C,N,V,hr,hC,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,_,_,hmatch,hpairs⟩ := hfamily n hn
  refine ⟨K,hK,?_⟩
  intro a ha
  obtain ⟨l,u,hpair,hl,hu,_,hfactor,_,hbound⟩ := hpairs a ha
  let c : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  let R : ℝ := Real.pi*(n : ℕ)*r
  have hR : 0 < R := by dsimp only [R]; positivity
  have hl' : ‖l-c‖ ≤ R/8 := by
    have hh : ‖l-c‖ < R/32 := by simpa only [mem_ball,dist_eq_norm] using hl
    linarith
  have hu' : ‖u-c‖ ≤ R/8 := by
    have hh : ‖u-c‖ < R/32 := by simpa only [mem_ball,dist_eq_norm] using hu
    linarith
  have hsub := closed_gap_ball_subset_energy_disc l u c R hR hl' hu'
  have hboundK (z : ℂ) (hz : z ∈ closedBall ((l+u)/2) ‖l-u‖) :
      ‖K (z,a)‖ ≤ 9*‖l-u‖^2/R^2 :=
    norm_two_zero_square_on_gap_ball (fun z => K (z,a))
      (twoZeroQuotient (fun z => K (z,a)) l u) l u z R (hfactor z) (hbound z (hsub hz)) hz
  refine ⟨l,u,hpair,hsub,hboundK,?_⟩
  intro z hz hdom
  have hsq := hmatch (z,a) ⟨⟨hsub hz,ha⟩,hdom⟩
  have hf := norm_le_gap_scale_of_square_bound _ (K (z,a)) ‖l-u‖ R (norm_nonneg _) hR
    hsq.symm (hboundK z hz)
  calc
    _ ≤ 3*‖l-u‖/R := hf
    _ = C*‖l-u‖/(n : ℕ) := by
      have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
      dsimp only [C,R]
      field_simp [Real.pi_ne_zero,hr.ne',hnpos.ne']

end NLS.KdV
