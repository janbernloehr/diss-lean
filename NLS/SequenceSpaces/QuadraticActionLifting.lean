import NLS.SequenceSpaces.SquareRootLifting

/-! # Openness and quantitative lifting of quadratic actions

The quadratic action map is an open surjection onto the half-exponent
Banach space. A change of actions can be lifted by changing only the
first coordinate sequence, with a uniform square-root distance bound.
-/
noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace NLS
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- Lift arbitrary actions near a prescribed complex coordinate pair,
keeping its second component fixed. The estimate includes all zero gaps. -/
theorem exists_nearby_quadraticActions (hp : p ≠ ⊤) (z : Coeff p × Coeff p) (b : Coeff q) :
    ∃ w : Coeff p × Coeff p, quadraticActionsExponent w = b ∧ w.2 = z.2 ∧
      ‖w-z‖^2 ≤ 2*‖b-quadraticActionsExponent z‖ := by
  obtain ⟨a,ha,hd⟩ := Coeff.exists_nearby_squareRoot hp z.1 ((2:ℂ) • b-Coeff.square z.2)
  refine ⟨(a,z.2),?_,rfl,?_⟩
  · ext n
    have hn := congrArg (fun c : Coeff q => c n) ha
    simp only [Coeff.square_apply,lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,Pi.smul_apply,
      smul_eq_mul] at hn
    rw [quadraticActionsExponent_apply]
    change (a n^2+z.2 n^2)/2 = b n
    linear_combination hn/2
  · have he : (2:ℂ) • b-Coeff.square z.2-Coeff.square z.1 =
        (2:ℂ) • (b-quadraticActionsExponent z) := by
      ext n
      simp only [lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
        Coeff.square_apply,quadraticActionsExponent_apply]
      ring
    rw [he,norm_smul] at hd
    have hn : ‖(a,z.2)-z‖ = ‖a-z.1‖ := by
      simp [Prod.norm_def]
    rw [hn]
    simpa using hd

/-- The quadratic action map reaches every complex half-exponent sequence. -/
theorem quadraticActionsExponent_surjective (hp : p ≠ ⊤) :
    Function.Surjective (quadraticActionsExponent (p := p) (q := q)) := by
  intro b
  obtain ⟨w,hw,_,_⟩ := exists_nearby_quadraticActions hp 0 b
  exact ⟨w,hw⟩

/-- A radius-squared action ball has lifts in the original coordinate ball. -/
theorem ball_subset_quadraticActionsExponent_image (hp : p ≠ ⊤)
    (z : Coeff p × Coeff p) {r : ℝ} (hr : 0 < r) :
    ball (quadraticActionsExponent (q := q) z) (r^2/2) ⊆
      quadraticActionsExponent '' ball z r := by
  intro b hb
  obtain ⟨w,hw,_,hd⟩ := exists_nearby_quadraticActions hp z b
  refine ⟨w,?_,hw⟩
  have hdist : ‖b-quadraticActionsExponent z‖ < r^2/2 := by
    simpa only [mem_ball,dist_eq_norm] using hb
  have hnorm : ‖w-z‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr.le).mp (by linarith)
  simpa only [mem_ball,dist_eq_norm] using hnorm

/-- Quadratic actions map every open coordinate set to an open action set. -/
theorem isOpenMap_quadraticActionsExponent (hp : p ≠ ⊤) :
    IsOpenMap (quadraticActionsExponent (p := p) (q := q)) := by
  intro U hU
  apply Metric.isOpen_iff.mpr
  rintro b ⟨z,hz,rfl⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU z hz
  exact ⟨r^2/2,by positivity,
    (ball_subset_quadraticActionsExponent_image hp z hr).trans (image_mono hball)⟩

/-- The quadratic action map realizes the topological quotient in the
Banach action norm. Analytic descent requires additional invariance arguments. -/
theorem isQuotientMap_quadraticActionsExponent (hp : p ≠ ⊤) :
    IsQuotientMap (quadraticActionsExponent (p := p) (q := q)) :=
  (isOpenMap_quadraticActionsExponent hp).isQuotientMap
    (continuousOn_univ.mp analyticOnNhd_quadraticActionsExponent.continuousOn)
    (quadraticActionsExponent_surjective hp)

end NLS
