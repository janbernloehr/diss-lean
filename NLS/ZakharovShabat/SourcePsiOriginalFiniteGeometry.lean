import NLS.ZakharovShabat.SourcePsiIsolatingFiniteGeometry
import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle

/-!
# Large-circle geometry in every original isolating family

Actual nested circles enclose the moving gaps inside the supplied original
disks. Their collars stay disjoint, and their exact free tail yields the
finite-hole geometry for every sufficiently large half-integer circle.
This works at complex sources and does not replace the original disks.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Nested circles in any supplied original disk family, fixed for all outer cutoffs. -/
structure SourcePsiOriginalCircleFamily (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (D : ℤ → Set ℂ) where
  circle : (m : ℤ) → SourceCriticalRootPeriodCircle hp hp1 ψ m
  outer : ℤ → ℝ
  collar : ∀ m, (circle m).radius < outer m
  closed_outer_subset : ∀ m, closedBall ((circle m).center:ℂ) (outer m) ⊆ D m
  disjoint_discs : ∀ m k, m ≠ k →
    Disjoint (closedBall ((circle m).center:ℂ) (outer m))
      (closedBall ((circle k).center:ℂ) (outer k))
  tail : ∃ N : ℕ, ∀ m : ℤ, N < m.natAbs →
    (circle m).center = Real.pi*m ∧ outer m < Real.pi/4

/-- Original gap containment constructs actual inner circles and analytic collars. -/
theorem SourceIsolatingNeighborhoods.nonempty_originalCircleFamily
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) : Nonempty (SourcePsiOriginalCircleFamily hp hp1 ψ D) := by
  classical
  obtain ⟨N,hN⟩ := hD.tail
  choose a r hr he using hD.discs
  let d (m : ℤ) : ℝ := if m.natAbs ≤ N then a m else Real.pi*m
  let q (m : ℤ) : ℝ := if m.natAbs ≤ N then r m else Real.pi/4
  have hq (m : ℤ) : 0 < q m := by
    dsimp only [q]
    split_ifs
    · exact hr m
    · positivity
  have heq (m : ℤ) : D m = ball (d m:ℂ) (q m) := by
    by_cases hm : m.natAbs ≤ N
    · simpa only [d,q,if_pos hm] using he m
    · simpa only [d,q,if_neg hm,refinedResonantDisk,Complex.ofReal_mul,Complex.ofReal_intCast] using hN m (by omega)
  have hex (m : ℤ) : ∃ u v : ℝ, 0 < u ∧ u < v ∧ v < q m ∧
      sourcePeriodicSegment hp hp1 ψ m ⊆ ball (d m:ℂ) u := by
    apply exists_nested_radii_of_segment_subset_ball
    simpa only [sourcePeriodicSegment,heq m] using hD.gap ψ hψ m
  choose u v hu huv hv hgap using hex
  let P (m : ℤ) : SourceCriticalRootPeriodCircle hp hp1 ψ m := {
    center := d m
    radius := u m
    radius_pos := hu m
    gap := hgap m
    other := by
      intro k hkm z hz
      rcases (hD.periodCircle ψ hψ m (d m) (q m) (hq m) (heq m)).other k hkm z hz with h | h
      · left; change z.re < d m-q m at h; linarith [huv m,hv m]
      · right; change d m+q m < z.re at h; linarith [huv m,hv m]
  }
  have hsub (m : ℤ) : closedBall ((P m).center:ℂ) (v m) ⊆ D m := by
    rw [heq m]
    intro z hz
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (hv m))
  refine ⟨⟨P,v,huv,hsub,fun m k hmk => (hD.disjoint m k hmk).mono (hsub m) (hsub k),N,?_⟩⟩
  intro m hm
  have hn : ¬m.natAbs ≤ N := by omega
  exact ⟨by simp only [P,d,if_neg hn],by simpa only [q,if_neg hn] using hv m⟩

namespace SourcePsiOriginalCircleFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {D : ℤ → Set ℂ}

/-- The original circles realize the actual finite-hole geometry at every large cutoff. -/
theorem eventually_finite_geometry (C : SourcePsiOriginalCircleFamily hp hp1 ψ D) :
    ∀ᶠ k : ℕ in atTop,
      SourcePsiFiniteGapCircleGeometry hp hp1 ψ 0 (centralCircleRadius k)
        (Finset.Icc (-(k:ℤ)) (k:ℤ)) (fun m => ((C.circle m).center:ℂ))
        (fun m => (C.circle m).radius) C.outer := by
  classical
  obtain ⟨N,hN⟩ := C.tail
  let B : ℝ := ∑ m ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (‖((C.circle m).center:ℂ)‖+C.outer m)
  have hhead m (hm : m.natAbs ≤ N) : ‖((C.circle m).center:ℂ)‖+C.outer m ≤ B := by
    dsimp only [B]
    apply Finset.single_le_sum (f := fun i : ℤ => ‖((C.circle i).center:ℂ)‖+C.outer i)
    · intro i _
      exact add_nonneg (norm_nonneg _) ((C.circle i).radius_pos.trans (C.collar i)).le
    · simp only [Finset.mem_Icc]; omega
  have hnorm (m : ℤ) : ‖(Real.pi:ℂ)*m‖ = Real.pi*(m.natAbs:ℝ) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      Complex.norm_intCast,Nat.cast_natAbs,Int.cast_abs]
  filter_upwards [eventually_ge_atTop N,tendsto_centralCircleRadius_atTop.eventually_ge_atTop (B+1)] with k hk hB
  refine ⟨(centralCircleRadius_pos k).le,(fun m _ => (C.circle m).radius_pos),
    (fun m _ => C.collar m),?_,(fun m _ j _ hmj => C.disjoint_discs m j hmj),
    (fun m _ => (C.circle m).gap),?_⟩
  · intro m hm z hz
    have hmabs : m.natAbs ≤ k := by simp only [Finset.mem_Icc] at hm; omega
    have hdist : ‖z-((C.circle m).center:ℂ)‖ ≤ C.outer m := by
      simpa only [mem_closedBall,dist_eq_norm] using hz
    have htri := norm_le_norm_sub_add z ((C.circle m).center:ℂ)
    rw [mem_ball,dist_zero_right]
    by_cases hmN : m.natAbs ≤ N
    · have hb := hhead m hmN
      linarith
    · obtain ⟨hc,hR⟩ := hN m (by omega)
      have hc' : ((C.circle m).center:ℂ) = (Real.pi:ℂ)*m := by exact_mod_cast hc
      rw [hc'] at hdist
      rw [hc',hnorm] at htri
      have hmk : (m.natAbs:ℝ) ≤ (k:ℝ) := by exact_mod_cast hmabs
      unfold centralCircleRadius
      nlinarith [Real.pi_pos]
  · intro m hm
    apply Set.disjoint_left.mpr
    intro z hz hzo
    have hmabs : k+1 ≤ m.natAbs := by simp only [Finset.mem_Icc] at hm; omega
    obtain ⟨hc,hR⟩ := hN m (by omega)
    have hc' : ((C.circle m).center:ℂ) = (Real.pi:ℂ)*m := by exact_mod_cast hc
    have hdist : ‖z-(Real.pi:ℂ)*m‖ < (C.circle m).radius := by
      simpa only [hc',mem_ball,dist_eq_norm] using (C.circle m).gap hz
    have hzo' : ‖z‖ ≤ centralCircleRadius k := by simpa only [mem_closedBall,dist_zero_right] using hzo
    have htri := norm_sub_norm_le ((Real.pi:ℂ)*m) z
    rw [hnorm,norm_sub_rev] at htri
    have hmk : (k:ℝ)+1 ≤ (m.natAbs:ℝ) := by exact_mod_cast hmabs
    have hr := C.collar m
    unfold centralCircleRadius at hzo'
    nlinarith [Real.pi_pos]

/-- The outer contour equals the finite sum of these original inner periods. -/
theorem eventually_decomposition (C : SourcePsiOriginalCircleFamily hp hp1 ψ D)
    (n : ℤ) (a : Coeff p) :
    ∀ᶠ k : ℕ in atTop,
      sourcePsiContour hp hp1 n a ψ 0 (centralCircleRadius k) =
        ∑ m ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
          sourcePsiContour hp hp1 n a ψ ((C.circle m).center:ℂ) (C.circle m).radius := by
  filter_upwards [C.eventually_finite_geometry] with k hk
  exact hk.decomposition n a

end SourcePsiOriginalCircleFamily
end NLS.ZakharovShabat
