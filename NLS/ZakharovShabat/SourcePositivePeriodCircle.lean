import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle
import NLS.ComplexAnalysis.RealDiameterDisc
import NLS.ZakharovShabat.SourceIndexedActionAnalytic

/-! # Positive refinements of actual source isolating circles

For a selected real gap with strictly positive left endpoint, every
existing isolating circle has a smaller real-centered replacement whose
closed disc is still inside the old open disc and lies strictly to the
right of zero. The argument includes collapsed gaps and preserves the
separation from every other source gap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceCriticalRootPeriodCircle.exists_positive_refinement
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (C : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (hleft : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).im = 0)
    (hright : (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).im = 0)
    (hpos : 0 < (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    ∃ D : SourceCriticalRootPeriodCircle hp hp1 ψ n,
      0 < D.center-D.radius ∧
      closedBall (D.center : ℂ) D.radius ⊆ ball (C.center : ℂ) C.radius := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hlr : l.re ≤ r.re := re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)).2.1 n)
  have hlC := re_bounds_of_mem_realCenteredBall (C.gap (left_mem_segment ℝ l r))
  have hrC := re_bounds_of_mem_realCenteredBall (C.gap (right_mem_segment ℝ l r))
  let a : ℝ := (max 0 (C.center-C.radius)+l.re)/2
  let b : ℝ := (r.re+C.center+C.radius)/2
  have hmax : max 0 (C.center-C.radius) < l.re := max_lt hpos hlC.1
  have ha0 : 0 < a := by dsimp [a]; linarith [le_max_left 0 (C.center-C.radius)]
  have haC : C.center-C.radius < a := by
    dsimp [a]; linarith [le_max_right 0 (C.center-C.radius)]
  have hal : a < l.re := by dsimp [a]; linarith
  have hrb : r.re < b := by dsimp [b]; linarith [hrC.2]
  have hbC : b < C.center+C.radius := by dsimp [b]; linarith [hrC.2]
  have hab : a < b := hal.trans_le (hlr.trans hrb.le)
  let d : ℝ := (a+b)/2
  let R : ℝ := (b-a)/2
  have hR : 0 < R := by dsimp [R]; linarith
  have hdl : d-R = a := by dsimp [d,R]; ring
  have hdr : d+R = b := by dsimp [d,R]; ring
  have hl : (l.re : ℂ) = l := by
    apply Complex.ext
    · rfl
    · exact hleft.symm
  have hr : (r.re : ℂ) = r := by
    apply Complex.ext
    · rfl
    · exact hright.symm
  have hlball : l ∈ ball (d : ℂ) R := by
    rw [← hl]
    exact (ofReal_mem_realDiameter_ball_iff a b l.re).mpr ⟨hal,hlr.trans_lt hrb⟩
  have hrball : r ∈ ball (d : ℂ) R := by
    rw [← hr]
    exact (ofReal_mem_realDiameter_ball_iff a b r.re).mpr ⟨hal.trans_le hlr,hrb⟩
  let D : SourceCriticalRootPeriodCircle hp hp1 ψ n := {
    center := d
    radius := R
    radius_pos := hR
    gap := (convex_ball (d : ℂ) R).segment_subset hlball hrball
    other := by
      intro m hm w hw
      rcases C.other m hm w hw with h | h
      · exact Or.inl (by rw [hdl]; linarith)
      · exact Or.inr (by rw [hdr]; linarith) }
  refine ⟨D,?_,?_⟩
  · change 0 < d-R
    rw [hdl]
    exact ha0
  · intro z hz
    have hdist : dist (d : ℂ) (C.center : ℂ)+R < C.radius := by
      rw [dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
      rcases le_total C.center d with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]
        linarith [hdr]
      · rw [abs_of_nonpos (sub_nonpos.mpr h)]
        linarith [hdl]
    have hzR : dist z (d : ℂ) ≤ R := mem_closedBall.mp hz
    have ht := dist_triangle z (d : ℂ) (C.center : ℂ)
    exact mem_ball.mpr (by linarith)

/-- Every positive real selected gap admits a strictly positive original
isolating circle, without assuming any geometry of a preselected circle. -/
theorem exists_positive_sourceCriticalRootPeriodCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hpos : 0 < (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    ∃ C : SourceCriticalRootPeriodCircle hp hp1 ψ n, 0 < C.center-C.radius := by
  obtain ⟨N,ε,_,_,V,_,_,hψV,c,hD⟩ :=
    exists_local_source_quantitative_isolating_discs hp hp1 ψ hreal
  obtain ⟨a,r,hr,he⟩ := hD.discs n
  let D := hD.periodCircle ψ hψV n a r hr he
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n
  obtain ⟨C,hC,_⟩ := D.exists_positive_refinement hends.1 hends.2 hpos
  exact ⟨C,hC⟩

end NLS.ZakharovShabat
