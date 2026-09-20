import NLS.ZakharovShabat.PeriodicEndpointPairOrdering

/-!
# Separation of periodic endpoint labels

Central endpoints lie between the real-part bounds of the central box.
Distant endpoints lie near their free centers. Increasing distinct indices
are therefore strictly separated whenever either index is distant.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}

/-- Either endpoint in the central block has real part strictly inside the central horizontal bounds. -/
theorem PeriodicEndpointLabeling.abs_re_central_lt (h : PeriodicEndpointLabeling hp φ N ξ η)
    (n : ℤ) (hn : n.natAbs ≤ N) (z : ℂ) (hz : ξ n = z ∨ η n = z) :
    |z.re| < centralCircleRadius N := by
  have hc := (h.central.root_iff z).mp ⟨n,hn,hz⟩
  exact ((mem_centralPeriodicSpectrum hp φ N z).mp hc).2.1

/-- Either distant endpoint has real part within a quarter pi of its free center. -/
theorem PeriodicEndpointLabeling.abs_re_distant_sub_lt (h : PeriodicEndpointLabeling hp φ N ξ η)
    (n : ℤ) (hn : N < n.natAbs) (z : ℂ) (hz : ξ n = z ∨ η n = z) :
    |z.re-Real.pi*n| < Real.pi/4 := by
  have hb : z ∈ refinedResonantDisk n := by
    rcases hz with rfl | rfl
    · exact (h.distant n hn).left_mem
    · exact (h.distant n hn).right_mem
  have hd : ‖z-(Real.pi : ℂ)*n‖ < Real.pi/4 := by simpa only [refinedResonantDisk, mem_ball, dist_eq_norm] using hb
  simpa only [sub_re, mul_re, ofReal_re, intCast_re, ofReal_im, intCast_im, mul_zero, sub_zero] using
    (Complex.abs_re_le_norm _).trans_lt hd

/-- Any endpoints at increasing indices are separated if at least one index is distant. -/
theorem PeriodicEndpointLabeling.re_lt_of_distant (h : PeriodicEndpointLabeling hp φ N ξ η)
    (i j : ℤ) (hij : i < j) (hd : N < i.natAbs ∨ N < j.natAbs)
    (x y : ℂ) (hx : ξ i = x ∨ η i = x) (hy : ξ j = y ∨ η j = y) : x.re < y.re := by
  by_cases hi : i.natAbs ≤ N
  · have hj : N < j.natAbs := hd.resolve_left (by omega)
    have hib := (abs_lt.mp (h.abs_re_central_lt i hi x hx)).2
    have hjb := (abs_lt.mp (h.abs_re_distant_sub_lt j hj y hy)).1
    have hjN : (N : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast (show (N : ℤ)+1 ≤ j by omega)
    unfold centralCircleRadius at hib
    nlinarith [Real.pi_pos]
  · have hi' : N < i.natAbs := by omega
    have hib := (abs_lt.mp (h.abs_re_distant_sub_lt i hi' x hx)).2
    by_cases hj : j.natAbs ≤ N
    · have hjb := (abs_lt.mp (h.abs_re_central_lt j hj y hy)).1
      have hiN : (i : ℝ) ≤ -(N : ℝ)-1 := by exact_mod_cast (show i ≤ -(N : ℤ)-1 by omega)
      unfold centralCircleRadius at hjb
      nlinarith [Real.pi_pos]
    · have hjb := (abs_lt.mp (h.abs_re_distant_sub_lt j (by omega) y hy)).1
      have hij' : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
      nlinarith [Real.pi_pos]

end NLS.ZakharovShabat
