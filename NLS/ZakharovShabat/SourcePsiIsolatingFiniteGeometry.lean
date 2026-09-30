import NLS.ZakharovShabat.SourcePsiIsolatingCircles
import NLS.ZakharovShabat.SourcePsiFiniteContourDecomposition
import NLS.ZakharovShabat.CentralCircleThresholds

/-!
# Finite large-circle geometry from the all-index isolating discs

The finitely many central assigned discs fit inside a sufficiently
large half-integer circle. Every remaining assigned disc has radius
pi/4 and center pi times its signed index. Consequently the large
circle encloses precisely the gaps at absolute index at most its
cutoff. The same inner and collar circles work for every later cutoff.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem mem_signed_cutoff_iff (m : ℤ) (k : ℕ) :
    m ∈ Finset.Icc (-(k : ℤ)) (k : ℤ) ↔ m.natAbs ≤ k := by
  rw [Finset.mem_Icc, ← abs_le, ← Int.natCast_natAbs]
  exact_mod_cast (Iff.rfl : m.natAbs ≤ k ↔ m.natAbs ≤ k)

private theorem norm_free_lattice_eq (m : ℤ) :
    ‖(Real.pi : ℂ)*m‖ = Real.pi*(m.natAbs : ℝ) := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]

namespace SourcePsiIsolatingCircleFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ ψ : CoeffPair p} {N : ℕ} {ε : ℝ}

/-- The constructed fixed circles instantiate the actual finite-hole
spectral geometry on every sufficiently large half-integer circle. -/
theorem eventually_finite_geometry
    (C : SourcePsiIsolatingCircleFamily hp hp1 φ ψ N ε) :
    ∀ᶠ k : ℕ in atTop,
      SourcePsiFiniteGapCircleGeometry hp hp1 ψ 0 (centralCircleRadius k)
        (Finset.Icc (-(k : ℤ)) (k : ℤ))
        (sourceIsolatingCenter hp hp1 φ N) C.inner C.outer := by
  classical
  let B : ℝ := ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (‖sourceIsolatingCenter hp hp1 φ N m‖ + sourceIsolatingRadius hp hp1 φ N ε m)
  have hhead m (hm : m.natAbs ≤ N) :
      ‖sourceIsolatingCenter hp hp1 φ N m‖ + sourceIsolatingRadius hp hp1 φ N ε m ≤ B := by
    dsimp only [B]
    apply Finset.single_le_sum (f := fun i : ℤ =>
      ‖sourceIsolatingCenter hp hp1 φ N i‖ + sourceIsolatingRadius hp hp1 φ N ε i)
    · intro i _
      have hT : 0 < sourceIsolatingRadius hp hp1 φ N ε i :=
        (C.inner_pos i).trans ((C.collar i).trans (C.outer_lt i))
      exact add_nonneg (norm_nonneg _) hT.le
    · exact (mem_signed_cutoff_iff m N).mpr hm
  filter_upwards [eventually_ge_atTop N,
    tendsto_centralCircleRadius_atTop.eventually_ge_atTop (B+1)] with k hk hB
  refine ⟨(centralCircleRadius_pos k).le,(fun m _ => C.inner_pos m),
    (fun m _ => C.collar m),?_,(fun m _ j _ hmj => C.disjoint_discs m j hmj),
    (fun m _ => C.gap_enclosed m),?_⟩
  · intro m hm z hz
    have hmabs := (mem_signed_cutoff_iff m k).mp hm
    have hdist : ‖z-sourceIsolatingCenter hp hp1 φ N m‖ ≤ C.outer m :=
      by simpa only [mem_closedBall,dist_eq_norm] using hz
    have htri := norm_le_norm_sub_add z (sourceIsolatingCenter hp hp1 φ N m)
    rw [mem_ball,dist_zero_right]
    by_cases hmN : m.natAbs ≤ N
    · have h := hhead m hmN
      have hlt := C.outer_lt m
      linarith
    · have hc : sourceIsolatingCenter hp hp1 φ N m = (Real.pi : ℂ)*m :=
        by simp only [sourceIsolatingCenter,if_neg hmN]
      have hR : C.outer m < Real.pi/4 :=
        by simpa only [sourceIsolatingRadius,if_neg hmN] using C.outer_lt m
      rw [hc] at hdist
      rw [hc,norm_free_lattice_eq] at htri
      have hmk : (m.natAbs : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmabs
      unfold centralCircleRadius
      nlinarith [Real.pi_pos]
  · intro m hm
    apply Set.disjoint_left.mpr
    intro z hz hzo
    have hmabs : k+1 ≤ m.natAbs := by
      have h := mt (mem_signed_cutoff_iff m k).mpr hm
      omega
    have hmN : ¬m.natAbs ≤ N := by omega
    have hc : sourceIsolatingCenter hp hp1 φ N m = (Real.pi : ℂ)*m :=
      by simp only [sourceIsolatingCenter,if_neg hmN]
    have hR : C.outer m < Real.pi/4 :=
      by simpa only [sourceIsolatingRadius,if_neg hmN] using C.outer_lt m
    have hdist : ‖z-(Real.pi : ℂ)*m‖ < C.inner m :=
      by simpa only [hc,mem_ball,dist_eq_norm] using C.gap_enclosed m hz
    have hnorm : ‖z‖ ≤ centralCircleRadius k :=
      by simpa only [mem_closedBall,dist_zero_right] using hzo
    have htri := norm_sub_norm_le ((Real.pi : ℂ)*m) z
    rw [norm_free_lattice_eq,norm_sub_rev] at htri
    have hmk : (k : ℝ)+1 ≤ (m.natAbs : ℝ) := by exact_mod_cast hmabs
    have hr := C.collar m
    unfold centralCircleRadius at hnorm
    nlinarith [Real.pi_pos]

/-- On every sufficiently large circle, the actual psi contour is the
finite sum of the fixed assigned gap contours. -/
theorem eventually_decomposition
    (C : SourcePsiIsolatingCircleFamily hp hp1 φ ψ N ε) (n : ℤ) (a : Coeff p) :
    ∀ᶠ k : ℕ in atTop,
      sourcePsiContour hp hp1 n a ψ 0 (centralCircleRadius k) =
        ∑ m ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
          sourcePsiContour hp hp1 n a ψ (sourceIsolatingCenter hp hp1 φ N m) (C.inner m) := by
  filter_upwards [C.eventually_finite_geometry] with k hG
  exact hG.decomposition n a

end SourcePsiIsolatingCircleFamily
end NLS.ZakharovShabat
