import NLS.ZakharovShabat.SourcePsiSingleVariation
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The free psi-contour Jacobian

At the free potential, moving one retained root changes the psi
integrand by a rational Cauchy kernel. Free-centered circles of radius
less than pi isolate one spectral point, so the scalar Jacobian is
diagonal. The normalization of (2.22) makes each diagonal entry two.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A free center of a different index lies outside a closed circle
of radius less than pi. -/
theorem freeCenter_not_mem_closedBall_other
    (m k : ℤ) (hmk : m ≠ k) (r : ℝ) (hrπ : r < Real.pi) :
    (Real.pi : ℂ)*k ∉ closedBall ((Real.pi : ℂ)*m) r := by
  intro h
  have hdist := mem_closedBall.mp h
  rw [dist_eq_norm, norm_free_center_sub] at hdist
  have habs : (1 : ℝ) ≤ |((k-m : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hmk))
  nlinarith [Real.pi_pos]

/-- No free center lies on a positive-radius free circle smaller than
the lattice spacing. -/
theorem freeCircle_point_ne_freeCenter
    (m k : ℤ) (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi)
    (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*m) r) :
    z ≠ (Real.pi : ℂ)*k := by
  by_cases hmk : m = k
  · subst k
    intro he
    have hdist := mem_sphere.mp hz
    rw [he, dist_self] at hdist
    exact (ne_of_gt hr) hdist.symm
  · intro he
    exact (freeCenter_not_mem_closedBall_other m k hmk r hrπ)
      (he ▸ sphere_subset_closedBall hz)

/-- The free-centered circle avoids every free periodic gap segment. -/
theorem freeCircle_subset_sourceCanonicalRootDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) :
    sphere ((Real.pi : ℂ)*m) r ⊆
      sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p) := by
  intro z hz k
  rw [sourcePeriodicSegment_zero_source hp hp1 k]
  exact freeCircle_point_ne_freeCenter m k r hr hrπ z hz

/-- The elementary Cauchy integral around a free-centered circle is
`2πi` for its own center and zero for every other center. -/
theorem freeCircle_sub_inv_integral
    (m k : ℤ) (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) :
    (∮ z in C((Real.pi : ℂ)*m,r),
      (z-(Real.pi : ℂ)*k)⁻¹) =
      if m = k then 2*Real.pi*I else 0 := by
  by_cases hmk : m = k
  · subst k
    rw [if_pos rfl]
    exact circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr)
  · rw [if_neg hmk]
    have hdiff : DifferentiableOn ℂ
        (fun z : ℂ => (z-(Real.pi : ℂ)*k)⁻¹)
        (closedBall ((Real.pi : ℂ)*m) r) := by
      intro z hz
      have hzk : z ≠ (Real.pi : ℂ)*k := by
        intro he
        exact (freeCenter_not_mem_closedBall_other m k hmk r hrπ) (he ▸ hz)
      have hs : DifferentiableAt ℂ
          (fun w : ℂ => w-(Real.pi : ℂ)*k) z := by fun_prop
      exact (hs.inv (sub_ne_zero.mpr hzk)).differentiableWithinAt
    exact (hdiff.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hr.le

/-- The two-pole kernel has only the residue at the moved root when
that root is the center of the free circle. -/
theorem freeCircle_two_inv_integral
    (m n k : ℤ) (hmn : m ≠ n) (hnk : n ≠ k)
    (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) :
    (∮ z in C((Real.pi : ℂ)*m,r),
      I * ((z-(Real.pi : ℂ)*n)⁻¹ *
        (z-(Real.pi : ℂ)*k)⁻¹)) =
      if m = k then
        (2*Real.pi : ℂ) /
          ((Real.pi : ℂ)*n-(Real.pi : ℂ)*k) else 0 := by
  let a : ℂ := (Real.pi : ℂ)*n
  let b : ℂ := (Real.pi : ℂ)*k
  let c : ℂ := (Real.pi : ℂ)*m
  have hab : a-b ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    dsimp [a,b]
    apply sub_ne_zero.mpr
    intro he
    have hcast : (n : ℂ) = k := mul_left_cancel₀ hπ he
    exact hnk (by exact_mod_cast hcast)
  have hcont (j : ℤ) : ContinuousOn
      (fun z : ℂ => (z-(Real.pi : ℂ)*j)⁻¹) (sphere c r) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.sub continuousOn_const
    · intro z hz
      exact sub_ne_zero.mpr (freeCircle_point_ne_freeCenter m j r hr hrπ z hz)
  have hintn : CircleIntegrable (fun z : ℂ => (z-a)⁻¹) c r :=
    (hcont n).circleIntegrable hr.le
  have hintk : CircleIntegrable (fun z : ℂ => (z-b)⁻¹) c r :=
    (hcont k).circleIntegrable hr.le
  have heq :
      (∮ z in C(c,r), I*((z-a)⁻¹*(z-b)⁻¹)) =
      ∮ z in C(c,r), I/(a-b)*((z-a)⁻¹-(z-b)⁻¹) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hza : z-a ≠ 0 := sub_ne_zero.mpr
      (freeCircle_point_ne_freeCenter m n r hr hrπ z hz)
    have hzb : z-b ≠ 0 := sub_ne_zero.mpr
      (freeCircle_point_ne_freeCenter m k r hr hrπ z hz)
    field_simp
    ring
  change (∮ z in C(c,r), I*((z-a)⁻¹*(z-b)⁻¹)) =
    if m = k then (2*Real.pi : ℂ)/(a-b) else 0
  rw [heq, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub hintn hintk,
    freeCircle_sub_inv_integral m n r hr hrπ,
    freeCircle_sub_inv_integral m k r hr hrπ]
  rw [if_neg hmn]
  by_cases hmk : m = k
  · rw [if_pos hmk, if_pos hmk]
    field_simp [hab]
    ring_nf
    simp [I_sq]
  · rw [if_neg hmk, if_neg hmk]
    simp

/-- The `(n-m)` weight in (2.22) turns the free two-pole residue
into the scalar diagonal value two. -/
theorem freeCircle_weighted_two_inv_integral
    (m n k : ℤ) (hmn : m ≠ n) (hnk : n ≠ k)
    (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) :
    ((n-m : ℤ) : ℂ) *
      (∮ z in C((Real.pi : ℂ)*m,r),
        I * ((z-(Real.pi : ℂ)*n)⁻¹ *
          (z-(Real.pi : ℂ)*k)⁻¹)) =
      if m = k then 2 else 0 := by
  rw [freeCircle_two_inv_integral m n k hmn hnk r hr hrπ]
  by_cases hmk : m = k
  · subst k
    rw [if_pos rfl, if_pos rfl]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hnm : ((n-m : ℤ) : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hmn))
    have hden : (Real.pi : ℂ)*n-(Real.pi : ℂ)*m =
        (Real.pi : ℂ)*(n-m : ℤ) := by push_cast; ring
    rw [hden]
    field_simp [hπ, hnm]
  · rw [if_neg hmk, if_neg hmk]
    simp

/-- On a free circle, varying one retained numerator root adds one
two-pole Cauchy kernel to the unperturbed one-pole integrand. -/
theorem sourcePsiContourIntegrandJoint_single_zero_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m n k : ℤ) (hkn : k ≠ n)
    (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi)
    (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*m) r) (t : ℂ) :
    sourcePsiContourIntegrandJoint hp hp1 n
      (z,((lp.single p k t : Coeff p),(0 : CoeffPair p))) =
      -I * (z-(Real.pi : ℂ)*n)⁻¹ +
        t * (I * ((z-(Real.pi : ℂ)*n)⁻¹ *
          (z-(Real.pi : ℂ)*k)⁻¹)) := by
  let a : ℂ := (Real.pi : ℂ)*n
  let b : ℂ := (Real.pi : ℂ)*k
  let root : ℂ := sourceCanonicalRoot hp hp1 (0 : CoeffPair p) z
  have hdom : z ∈ sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p) :=
    freeCircle_subset_sourceCanonicalRootDomain hp hp1 m r hr hrπ hz
  have hroot : root ≠ 0 :=
    sourceCanonicalRoot_ne_zero_off_gaps hp hp1 0 z hdom
  have hzb : z ≠ b := freeCircle_point_ne_freeCenter m k r hr hrπ z hz
  have hden : b-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzb)
  have hbase : sourcePsiFree n z / root = -I*(z-a)⁻¹ := by
    rw [sourcePsiFree_div_sourceCanonicalRoot_zero_source hp hp1 n z hdom,
      sourceStandardRoot_zero_source hp hp1 n z]
    change I*(a-z)⁻¹ = -I*(z-a)⁻¹
    rw [show a-z = -(z-a) by ring, inv_neg]
    ring
  change sourcePsiCandidate n
      (z,(lp.single p k t : Coeff p)) / root =
    -I*(z-a)⁻¹ + t*(I*((z-a)⁻¹*(z-b)⁻¹))
  rw [sourcePsiCandidate_single_variation hp hp1 n k hkn z t hzb]
  calc
    (sourcePsiFree n z + t * (sourcePsiFree n z / (b-z))) / root =
        sourcePsiFree n z / root + t*((sourcePsiFree n z / root)/(b-z)) := by
          field_simp [hroot, hden]
    _ = -I*(z-a)⁻¹ + t*((-I*(z-a)⁻¹)/(b-z)) := by rw [hbase]
    _ = -I*(z-a)⁻¹ + t*(I*((z-a)⁻¹*(z-b)⁻¹)) := by
      rw [show b-z = -(z-b) by ring, div_neg]
      ring

/-- Every scalar contour equation is exactly linear along a single
retained free root coordinate, with slope two on the matching contour
and zero on all other free-centered contours. -/
theorem sourcePsiEquationCoordinate_single_zero_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m n k : ℤ) (hmn : m ≠ n) (hkn : k ≠ n)
    (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) (t : ℂ) :
    sourcePsiEquationCoordinate hp hp1 n m
      (lp.single p k t : Coeff p) (0 : CoeffPair p)
      ((Real.pi : ℂ)*m) r =
      t * (if m = k then 2 else 0) := by
  let c : ℂ := (Real.pi : ℂ)*m
  let base : ℂ → ℂ := fun z => -I*(z-(Real.pi : ℂ)*n)⁻¹
  let variation : ℂ → ℂ := fun z =>
    I*((z-(Real.pi : ℂ)*n)⁻¹*(z-(Real.pi : ℂ)*k)⁻¹)
  have hinv (j : ℤ) : ContinuousOn
      (fun z : ℂ => (z-(Real.pi : ℂ)*j)⁻¹) (sphere c r) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.sub continuousOn_const
    · intro z hz
      exact sub_ne_zero.mpr (freeCircle_point_ne_freeCenter m j r hr hrπ z hz)
  have hbaseInt : CircleIntegrable base c r :=
    (continuousOn_const.mul (hinv n)).circleIntegrable hr.le
  have hvariationCont : ContinuousOn variation (sphere c r) :=
    continuousOn_const.mul ((hinv n).mul (hinv k))
  have hvariationInt : CircleIntegrable
      (fun z => t*variation z) c r :=
    (continuousOn_const.mul hvariationCont).circleIntegrable hr.le
  have hInt :
      (∮ z in C(c,r), sourcePsiContourIntegrandJoint hp hp1 n
        (z,((lp.single p k t : Coeff p),(0 : CoeffPair p)))) =
      ∮ z in C(c,r), base z+t*variation z := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    exact sourcePsiContourIntegrandJoint_single_zero_eq
      hp hp1 m n k hkn r hr hrπ z hz t
  have hbaseZero : (∮ z in C(c,r), base z) = 0 := by
    change (∮ z in C(c,r), -I*(z-(Real.pi : ℂ)*n)⁻¹) = 0
    rw [circleIntegral.integral_const_mul,
      freeCircle_sub_inv_integral m n r hr hrπ, if_neg hmn]
    simp
  rw [sourcePsiEquationCoordinate_eq_raw_circleIntegral, hInt,
    circleIntegral.integral_add hbaseInt hvariationInt,
    hbaseZero, zero_add, circleIntegral.integral_const_mul]
  calc
    ((n-m : ℤ) : ℂ) * (t*(∮ z in C(c,r), variation z)) =
        t * (((n-m : ℤ) : ℂ) * (∮ z in C(c,r), variation z)) := by ring
    _ = t * (if m = k then 2 else 0) := by
      rw [freeCircle_weighted_two_inv_integral m n k hmn (Ne.symm hkn) r hr hrπ]

/-- The scalar Jacobian entry at the free data: two on the diagonal
and zero off it. -/
theorem hasDerivAt_sourcePsiEquationCoordinate_single_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m n k : ℤ) (hmn : m ≠ n) (hkn : k ≠ n)
    (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) :
    HasDerivAt
      (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
        (lp.single p k t : Coeff p) (0 : CoeffPair p)
        ((Real.pi : ℂ)*m) r)
      (if m = k then 2 else 0) 0 := by
  have heq : (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
      (lp.single p k t : Coeff p) (0 : CoeffPair p)
      ((Real.pi : ℂ)*m) r) =
      (fun t : ℂ => t*(if m = k then 2 else 0)) := by
    funext t
    exact sourcePsiEquationCoordinate_single_zero_eq
      hp hp1 m n k hmn hkn r hr hrπ t
  rw [heq]
  simpa using (hasDerivAt_id (0 : ℂ)).mul_const (if m = k then 2 else 0)

/-- The same Jacobian entry, expressed on the dissertation's
omitted-coordinate Banach parameter space. -/
theorem hasDerivAt_sourcePsiDeletedEquationCoordinate_single_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m n k : ℤ) (hmn : m ≠ n) (hkn : k ≠ n)
    (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) :
    HasDerivAt
      (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (Coeff.deletedSingleCLM n k hkn t) (0 : CoeffPair p)
        ((Real.pi : ℂ)*m) r)
      (if m = k then 2 else 0) 0 := by
  change HasDerivAt
    (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
      (lp.single p k t : Coeff p) (0 : CoeffPair p)
      ((Real.pi : ℂ)*m) r)
    (if m = k then 2 else 0) 0
  exact hasDerivAt_sourcePsiEquationCoordinate_single_zero
    hp hp1 m n k hmn hkn r hr hrπ

end NLS.ZakharovShabat
