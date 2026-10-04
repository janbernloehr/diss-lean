import NLS.SequenceSpaces.QuadraticActionsExponent
import NLS.ComplexAnalysis.NearbySquareRoot

/-! # Quantitative square-root lifting in sequence spaces

Coordinatewise squaring maps lp onto l(p/2). Nearby action values admit
nearby lifts, including at infinitely many zero coordinates. No global
continuous choice of square roots is assumed.
-/
noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- The real exponents in a doubling Holder triple differ by a factor two. -/
theorem doublingExponent_toReal : p.toReal = 2*q.toReal := by
  let : p.HolderTriple p (p/2) := holderTriple_half p
  have he : q = p/2 := ENNReal.HolderTriple.unique p p q (p/2)
  rw [he,ENNReal.toReal_div]
  norm_num
  ring

/-- Coordinatewise squaring with its natural Banach target. -/
def square (a : Coeff p) : Coeff q := doublingProduct a a

@[simp] theorem square_apply (a : Coeff p) (n : ℤ) : square (q := q) a n = a n ^ 2 := by
  change a n*a n = _
  ring

/-- Squaring is an entire Banach-space polynomial. -/
theorem analyticOnNhd_square : AnalyticOnNhd ℂ (square (p := p) (q := q)) univ := by
  intro a _
  exact ((doublingProduct (p := q) (q := p)).analyticAt_bilinear _).comp₂ analyticAt_id analyticAt_id

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
private theorem exponent_pow (x : ℝ) (hx : 0 ≤ x) : x ^ p.toReal = (x^2) ^ q.toReal := by
  rw [← Real.rpow_two,← Real.rpow_mul hx,← doublingExponent_toReal (p := p) (q := q)]

omit [Fact (1 ≤ q)] in
/-- Square domination in the half-exponent space gives membership at the
original exponent. -/
theorem memℓp_of_norm_sq_le (hp : p ≠ ⊤) (b : Coeff q) (f : ℤ → ℂ)
    (h : ∀ n, ‖f n‖^2 ≤ ‖b n‖) : Memℓp f p := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  have hq0 : 0 < q.toReal := by
    have he := doublingExponent_toReal (p := p) (q := q)
    linarith
  apply memℓp_gen
  apply Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) _) _
    ((lp.memℓp b).summable hq0)
  intro n
  rw [exponent_pow (p := p) (q := q) _ (norm_nonneg _)]
  exact Real.rpow_le_rpow (sq_nonneg _) (h n) hq0.le

/-- The pointwise square bound gives the sharp sequence norm bound. -/
theorem norm_sq_le_of_norm_sq_le (hp : p ≠ ⊤) (a : Coeff p) (b : Coeff q)
    (h : ∀ n, ‖a n‖^2 ≤ ‖b n‖) : ‖a‖^2 ≤ ‖b‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  have hq0 : 0 < q.toReal := by
    have he := doublingExponent_toReal (p := p) (q := q)
    linarith
  apply (Real.rpow_le_rpow_iff (sq_nonneg _) (norm_nonneg _) hq0).mp
  rw [← exponent_pow (p := p) (q := q) _ (norm_nonneg _),
    lp.norm_rpow_eq_tsum hp0,lp.norm_rpow_eq_tsum hq0]
  apply Summable.tsum_le_tsum _ ((lp.memℓp a).summable hp0) ((lp.memℓp b).summable hq0)
  intro n
  rw [exponent_pow (p := p) (q := q) _ (norm_nonneg _)]
  exact Real.rpow_le_rpow (sq_nonneg _) (h n) hq0.le

/-- Every nearby squared sequence has a lift close to a prescribed
sequence, with the exact square-root modulus of continuity. -/
theorem exists_nearby_squareRoot (hp : p ≠ ⊤) (a : Coeff p) (b : Coeff q) :
    ∃ w : Coeff p, square (q := q) w = b ∧ ‖w-a‖^2 ≤ ‖b-square a‖ := by
  classical
  choose w hw hb using fun n => ComplexAnalysis.exists_nearby_squareRoot (a n) (b n)
  have hmem : Memℓp (fun n => w n-a n) p :=
    memℓp_of_norm_sq_le hp (b-square a) _ (by simpa using hb)
  let d : Coeff p := ⟨fun n => w n-a n,hmem⟩
  refine ⟨a+d,?_,?_⟩
  · ext n
    simp only [square_apply,lp.coeFn_add,Pi.add_apply]
    change (a n+(w n-a n))^2 = b n
    simpa only [add_sub_cancel] using hw n
  · rw [add_sub_cancel_left]
    exact norm_sq_le_of_norm_sq_le hp d (b-square a) (by simpa [d] using hb)

/-- Squaring is onto the full half-exponent space, also at zero. -/
theorem square_surjective (hp : p ≠ ⊤) : Function.Surjective (square (p := p) (q := q)) := by
  intro b
  obtain ⟨w,hw,_⟩ := exists_nearby_squareRoot hp (0 : Coeff p) b
  exact ⟨w,hw⟩

/-- A squared-radius ball is contained in the image of the original ball. -/
theorem ball_subset_square_image (hp : p ≠ ⊤) (a : Coeff p) {r : ℝ} (hr : 0 < r) :
    ball (square (q := q) a) (r^2) ⊆ square '' ball a r := by
  intro b hb
  obtain ⟨w,hw,hd⟩ := exists_nearby_squareRoot hp a b
  refine ⟨w,?_,hw⟩
  have hdist : ‖b-square a‖ < r^2 := by simpa only [mem_ball,dist_eq_norm] using hb
  have hnorm : ‖w-a‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr.le).mp (hd.trans_lt hdist)
  simpa only [mem_ball,dist_eq_norm] using hnorm

/-- Coordinatewise squaring is open, despite its vanishing derivative at zero. -/
theorem isOpenMap_square (hp : p ≠ ⊤) : IsOpenMap (square (p := p) (q := q)) := by
  intro U hU
  apply Metric.isOpen_iff.mpr
  rintro b ⟨a,ha,rfl⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU a ha
  exact ⟨r^2,sq_pos_of_pos hr,(ball_subset_square_image hp a hr).trans (image_mono hball)⟩

/-- Squaring is a topological quotient map in the Banach norms. -/
theorem isQuotientMap_square (hp : p ≠ ⊤) : IsQuotientMap (square (p := p) (q := q)) :=
  (isOpenMap_square hp).isQuotientMap
    (continuousOn_univ.mp analyticOnNhd_square.continuousOn) (square_surjective hp)

/-- Continuity of a function of squared coordinates can be checked on
its lifted function. This statement does not assert analytic descent. -/
theorem continuous_iff_comp_square (hp : p ≠ ⊤) {F : Type*} [TopologicalSpace F]
    (f : Coeff q → F) : Continuous f ↔ Continuous (f ∘ square (p := p)) :=
  (isQuotientMap_square hp).continuous_iff

end NLS.Coeff
