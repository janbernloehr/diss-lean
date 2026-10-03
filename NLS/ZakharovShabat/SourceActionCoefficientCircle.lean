import NLS.ZakharovShabat.SourceCanonicalCoefficientContinuity
import NLS.ZakharovShabat.SourceRealActionRealCenteredCircle

/-! # Fixed action contours under bounded coefficient limits

The converging selected endpoints stay inside one real-centered circle.
Convergence of the two neighboring endpoints and real spectral ordering keep
every other gap outside its closed disc. Thus the same circle computes the
selected action at the limit and eventually throughout the approximating
family. Convergence of the integrand is still a separate spectral obligation.
-/
noncomputable section
open Set Filter Topology Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Separation from the adjacent real gaps excludes every other gap from the
closed disc, by the global ordering of canonical periodic endpoints. -/
theorem closedBall_subset_sourceOmittedDomain_of_neighbor_separation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (c : ℂ) (R : ℝ)
    (hc : c.im = 0)
    (hprev : (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n-1)).re < c.re-R)
    (hnext : c.re+R < (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re) :
    closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ n := by
  intro z hz m hmn hmem
  have hzim := sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ hφ m z hmem
  have hproj : |z.re-c.re| ≤ R := by
    rw [← sourceRealPoints_dist_eq_abs_re_sub z c hzim hc]
    exact mem_closedBall.mp hz
  have hbounds := abs_le.mp hproj
  have hI := sourcePeriodicSegment_re_mem_Icc hp hp1 φ m z hmem
  rcases lt_or_gt_of_ne hmn with hm | hm
  · have hzu : z.re ≤ (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n-1)).re := by
      by_cases he : m = n-1
      · subst m
        exact hI.2
      · have hord := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) (by omega : m < n-1)
        have hwithin := re_le_of_complexLexLE
          ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).2.1 (n-1))
        exact hI.2.trans (hord.le.trans hwithin)
    linarith
  · have hvz : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re ≤ z.re := by
      by_cases he : m = n+1
      · subst m
        exact hI.1
      · have hord := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) (by omega : n+1 < m)
        have hwithin := re_le_of_complexLexLE
          ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).2.1 (n+1))
        exact (hwithin.trans hord.le).trans hI.1
    linarith

/-- Every indexed action has one fixed real-centered isolating circle valid
at the coefficient limit and eventually at all approximants. This constructs
the circle and its full gap-avoidance conditions, including at collapsed gaps. -/
theorem exists_source_actionCircle_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax p (φ k))) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n))) (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ c.im = 0 ∧
      (sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
        closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n ∧
        sourceRealAction hp hp1 ψ hψ n = sourceActionCircle hp hp1 ψ c R) ∧
      ∀ᶠ k in l, sourcePeriodicSegment hp hp1 (φ k) n ⊆ ball c R ∧
        closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 (φ k) n ∧
        sourceRealAction hp hp1 (φ k) (hφ k) n = sourceActionCircle hp hp1 (φ k) c R := by
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let U := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let a := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (n-1)).re
  let b := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (n+1)).re
  have ha : a < L.re := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hψ) (by omega : n-1 < n)
  have hb' : U.re < b := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hψ) (by omega : n < n+1)
  let ε := min (L.re-a) (b-U.re) / 2
  have hε : 0 < ε := div_pos (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb')) (by norm_num)
  let c : ℂ := (((L.re+U.re)/2 : ℝ) : ℂ)
  let d := (U.re-L.re)/2
  let R := d+ε
  have hd : 0 ≤ d := by
    have hw := re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ)).2.1 n)
    change L.re ≤ U.re at hw
    dsimp [d]
    linarith
  have hR : 0 < R := by dsimp [R]; linarith
  have hc : c.im = 0 := by simp [c]
  have hap : a < c.re-R := by
    dsimp [c,R,d,ε]
    linarith [min_le_left (L.re-a) (b-U.re)]
  have hbn : c.re+R < b := by
    dsimp [c,R,d,ε]
    linarith [min_le_right (L.re-a) (b-U.re)]
  have hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R :=
    sourcePeriodicSegment_subset_midpoint_ball hp hp1 ψ hψ n ε hε
  have hother := closedBall_subset_sourceOmittedDomain_of_neighbor_separation hp hp1 ψ hψ n c R hc hap hbn
  refine ⟨c,R,hR,hc,⟨hseg,hother,sourceRealAction_eq_realCentered_enclosingCircle hp hp1 ψ hψ n c R hc hR hseg hother⟩,?_⟩
  have hends := tendsto_source_canonicalPeriodicEndpoints_of_bounded_coefficientwise hp hp1 φ ψ hb hφ hψ ht n
  have hprev := (tendsto_source_canonicalPeriodicEndpoints_of_bounded_coefficientwise hp hp1 φ ψ hb hφ hψ ht (n-1)).2
  have hnext := (tendsto_source_canonicalPeriodicEndpoints_of_bounded_coefficientwise hp hp1 φ ψ hb hφ hψ ht (n+1)).1
  have hL := hends.1.eventually (isOpen_ball.mem_nhds (hseg (left_mem_segment ℝ L U)))
  have hU := hends.2.eventually (isOpen_ball.mem_nhds (hseg (right_mem_segment ℝ L U)))
  have hprev' := (continuous_re.continuousAt.tendsto.comp hprev).eventually (gt_mem_nhds hap)
  have hnext' := (continuous_re.continuousAt.tendsto.comp hnext).eventually (lt_mem_nhds hbn)
  filter_upwards [hL,hU,hprev',hnext'] with k hkL hkU hkprev hknext
  have hsegk : sourcePeriodicSegment hp hp1 (φ k) n ⊆ ball c R :=
    (convex_ball c R).segment_subset hkL hkU
  have hotherk := closedBall_subset_sourceOmittedDomain_of_neighbor_separation hp hp1 (φ k) (hφ k) n c R hc hkprev hknext
  exact ⟨hsegk,hotherk,sourceRealAction_eq_realCentered_enclosingCircle hp hp1 (φ k) (hφ k) n c R hc hR hsegk hotherk⟩

end NLS.ZakharovShabat
