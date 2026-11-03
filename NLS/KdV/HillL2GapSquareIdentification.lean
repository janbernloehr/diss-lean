import NLS.KdV.HillL2HighGapPairs
import NLS.KdV.ClassicalHillWholeGapSquares
import NLS.KdV.HillL2CutSquareTrace

/-! # Identifying the shared high-gap charts with intrinsic real Hill gaps

The complex unordered pair encloses both intrinsic real endpoints. Its
order is therefore the intrinsic order or its reverse on an open gap.
The two analytic squared primitives agree by local inverse uniqueness
at an endpoint and the identity theorem on their common domain.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillClosedBall_subset_hillL2HighEnergyRegion (n : ℕ+) :
    closedBall (freeHillValue (n : ℕ) : ℂ) (n : ℝ) ⊆ hillL2HighEnergyRegion n := by
  intro z hz
  have hn : (0 : ℝ) < (n : ℕ) := by positivity
  have hpi : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hc : (((Real.pi : ℂ) * (n : ℕ)) ^ 2) = (freeHillValue (n : ℕ) : ℂ) := by
    simp only [freeHillValue, Int.cast_natCast]
    push_cast
    ring
  have hz' : z ∈ ball (((Real.pi : ℂ) * (n : ℕ)) ^ 2)
      (Real.pi * (n : ℕ) * (Real.pi / 4)) := by
    rw [hc, mem_ball]
    have hd := mem_closedBall.mp hz
    nlinarith [mul_lt_mul_of_pos_right hpi hn]
  have hs := sqrt_mem_ball_of_energy_disc (Real.pi * (n : ℕ)) (Real.pi / 4)
    (by positivity) z (by simpa only [ofReal_mul, ofReal_natCast] using hz')
  refine ⟨Complex.sqrt z, ?_, complex_sqrt_sq z⟩
  simpa only [ofReal_mul, ofReal_natCast] using hs

theorem HillL2HighGapPair.eq_or_swap_real
    {q : Coeff 2} {n : ℕ+} {l u : ℂ} (hpair : HillL2HighGapPair q n l u)
    (p : HillRealHighGapPair q (n : ℕ)) (hopen : p.left ≠ p.right) :
    (l = (p.left : ℂ) ∧ u = (p.right : ℂ)) ∨
      (l = (p.right : ℂ) ∧ u = (p.left : ℂ)) := by
  have hl := (hpair.zeros_iff _ (hillClosedBall_subset_hillL2HighEnergyRegion n p.left_mem)).mp p.left_zero
  have hu := (hpair.zeros_iff _ (hillClosedBall_subset_hillL2HighEnergyRegion n p.right_mem)).mp p.right_zero
  have hne : (p.left : ℂ) ≠ (p.right : ℂ) := fun he => hopen (ofReal_injective he)
  rcases hl with hl | hl <;> rcases hu with hu | hu
  · exact (hne (hl.trans hu.symm)).elim
  · exact Or.inl ⟨hl.symm, hu.symm⟩
  · exact Or.inr ⟨hu.symm, hl.symm⟩
  · exact (hne (hl.trans hu.symm)).elim

/-- An analytic square satisfying the same trace equation and zero
normalization agrees with the actual filled high-gap square. -/
theorem HillL2NormalizedCutPrimitive.square_eq_on_of_trace_and_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16 * ‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ) (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (K : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hsub : U ⊆ ball (freeHillValue n : ℂ) (7 * (n : ℝ) / 8))
    (hl : (p.left : ℂ) ∈ U) (hK : AnalyticOnNhd ℂ K U) (hK0 : K p.left = 0)
    (htrace : ∀ z ∈ U, squaredCosh (K z) =
      (-1 : ℂ) ^ n * hillL2Discriminant (SpectralWeight.one.toCoeff q) z / 2) :
    EqOn K (hillL2CutPrimitiveSquare n p.left p.right F) U := by
  let X := hillL2CutPrimitiveSquare n p.left p.right F
  obtain ⟨hX, _, hX0, _⟩ := h.square_extension q hq hr n hn hcut p hopen R F
  have heq : K =ᶠ[𝓝 (p.left : ℂ)] X := by
    apply eventuallyEq_of_squaredCosh_eq K X p.left
      (hK p.left hl).continuousAt (hX p.left (hsub hl)).continuousAt hK0 hX0
    filter_upwards [hU.mem_nhds hl] with z hz
    exact (htrace z hz).trans (h.square_trace q hq hr n hn hcut p hopen R F z (hsub hz)).symm
  exact hK.eqOn_of_preconnected_of_eventuallyEq (hX.mono hsub) hconn hl heq

end NLS.KdV
