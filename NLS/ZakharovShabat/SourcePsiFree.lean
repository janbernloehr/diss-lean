import NLS.ZakharovShabat.SourceDeletedFreeSine
import NLS.ZakharovShabat.SourceNormalizedActionFree
import NLS.ZakharovShabat.SourceStandardRootContourBasic
import NLS.ZakharovShabat.FreeSineQuotientAnalytic
import NLS.ZakharovShabat.FreeDerivativeZeroCounts

/-!
# The free psi-functions of Theorem 12.1

At zero potential the numerator with its `n`th zero omitted is the
filled sine quotient. The standard root is `-2i sin z`, so its quotient
with the free psi-function has a single Cauchy pole. This gives the
normalization and orthogonality contour integrals at the free potential.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The free psi-function, with the normalization of (2.20). -/
def sourcePsiFree (n : ℤ) (z : ℂ) : ℂ := -2 * freeSineQuotient n z

/-- Every free psi-function is entire, including at its omitted zero. -/
theorem differentiable_sourcePsiFree (n : ℤ) :
    Differentiable ℂ (sourcePsiFree n) := by
  exact (differentiable_freeSineQuotient n).const_mul (-2)

/-- The omitted free zero is filled with a nonzero value. -/
theorem sourcePsiFree_center_ne_zero (n : ℤ) :
    sourcePsiFree n ((Real.pi : ℂ)*n) ≠ 0 := by
  rw [sourcePsiFree, freeSineQuotient_center]
  intro h
  have hc : cos ((Real.pi : ℂ)*n) = 0 :=
    (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hn := norm_cos_freeCenter n
  rw [hc, norm_zero] at hn
  norm_num at hn

/-- Every other free lattice point is a zero of the indexed psi-function. -/
theorem sourcePsiFree_other_center_eq_zero (n m : ℤ) (hmn : m ≠ n) :
    sourcePsiFree n ((Real.pi : ℂ)*m) = 0 := by
  have hcenter : (Real.pi : ℂ)*m ≠ (Real.pi : ℂ)*n := by
    intro he
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hcast : (m : ℂ) = n := mul_left_cancel₀ hπ he
    exact hmn (by exact_mod_cast hcast)
  rw [sourcePsiFree, freeSineQuotient_eq_div n _ hcenter]
  have hs : sin ((Real.pi : ℂ)*m) = 0 := by
    rw [mul_comm]
    exact Complex.sin_int_mul_pi m
  rw [hs]
  simp

/-- The free canonical root has the sign fixed by the standard-root product. -/
theorem sourceCanonicalRoot_zero_source_eq_free_sine
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (z : ℂ) :
    sourceCanonicalRoot hp hp1 (0 : CoeffPair p) z = -2*I*sin z := by
  rw [sourceCanonicalRoot_eq_omitted hp hp1 n,
    sourceStandardRoot_zero_source hp hp1 n z,
    sourceStandardRootOmittedProduct_zero_source_eq_deleted hp hp1 n z,
    (congrFun (jointDeletedSingleSpectralProduct_zero_eq_freeSineQuotient hp hp1 n) z)]
  calc
    2*I*((Real.pi : ℂ)*n-z)*freeSineQuotient n z =
      -2*I*(freeSineQuotient n z*(z-(Real.pi : ℂ)*n)) := by ring
    _ = -2*I*sin z := by rw [freeSineQuotient_mul_sub]

/-- The free psi-function has exactly the prescribed deleted-product
normalization, not merely the same zeros. -/
theorem sourcePsiFree_eq_deleted_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (z : ℂ) :
    sourcePsiFree n z =
      -2 * jointDeletedSingleSpectralProduct n (z,(0 : Coeff p)) := by
  rw [(congrFun (jointDeletedSingleSpectralProduct_zero_eq_freeSineQuotient hp hp1 n) z)]
  rfl

/-- Away from all free gaps, the quotient in (2.21) is the Cauchy
kernel of the indexed standard root. -/
theorem sourcePsiFree_div_sourceCanonicalRoot_zero_source
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p)) :
    sourcePsiFree n z / sourceCanonicalRoot hp hp1 (0 : CoeffPair p) z =
      I * (sourceStandardRoot hp hp1 (0 : CoeffPair p) n z)⁻¹ := by
  have hs : sourceStandardRoot hp hp1 (0 : CoeffPair p) n z ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 0 n z (hz n)
  have ho : sourceStandardRootOmittedProduct hp hp1 n (0 : CoeffPair p) z ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 0 z n
      (fun m hm => hz m)
  have hfree : sourcePsiFree n z =
      -2 * sourceStandardRootOmittedProduct hp hp1 n (0 : CoeffPair p) z := by
    rw [sourceStandardRootOmittedProduct_zero_source_eq_deleted hp hp1 n z,
      (congrFun (jointDeletedSingleSpectralProduct_zero_eq_freeSineQuotient hp hp1 n) z)]
    rfl
  rw [hfree, sourceCanonicalRoot_eq_omitted hp hp1 n]
  field_simp [hs, ho]
  simp [I_sq]

/-- The free contour functional is the normalization in (2.21). -/
def sourcePsiFreeContour
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℂ) (r : ℝ) : ℂ :=
  ((2*Real.pi : ℂ)⁻¹) *
    ∮ z in C(c,r), sourcePsiFree n z /
      sourceCanonicalRoot hp hp1 (0 : CoeffPair p) z

/-- On a circle avoiding the free spectral lattice, the psi integral
reduces to the inverse-standard-root integral. -/
theorem sourcePsiFreeContour_eq_standardRoot_integral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r)
    (hcircle : sphere c r ⊆ sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p)) :
    sourcePsiFreeContour hp hp1 n c r =
      (2*Real.pi : ℂ)⁻¹ * I *
        (∮ z in C(c,r),
          (sourceStandardRoot hp hp1 (0 : CoeffPair p) n z)⁻¹) := by
  unfold sourcePsiFreeContour
  have heq :
      (∮ z in C(c,r), sourcePsiFree n z /
        sourceCanonicalRoot hp hp1 (0 : CoeffPair p) z) =
      ∮ z in C(c,r), I *
        (sourceStandardRoot hp hp1 (0 : CoeffPair p) n z)⁻¹ := by
    apply circleIntegral.integral_congr hr
    intro z hz
    exact sourcePsiFree_div_sourceCanonicalRoot_zero_source hp hp1 n z (hcircle hz)
  rw [heq, circleIntegral.integral_const_mul]
  ring

/-- The diagonal free psi contour has value one. -/
theorem sourcePsiFreeContour_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r)
    (hcircle : sphere c r ⊆ sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p))
    (hmid : (Real.pi : ℂ)*n ∈ ball c r) :
    sourcePsiFreeContour hp hp1 n c r = 1 := by
  rw [sourcePsiFreeContour_eq_standardRoot_integral hp hp1 n c r hr hcircle]
  have hgap : canonicalPeriodicGap hp hp1
      (periodOnePotential (0 : CoeffPair p))
      (periodOnePotential_mem (0 : CoeffPair p)) n = 0 := by
    simp only [map_zero]
    exact canonicalPeriodicGap_zero hp hp1 n
  have hmid' : canonicalPeriodicMidpoint hp hp1
      (periodOnePotential (0 : CoeffPair p))
      (periodOnePotential_mem (0 : CoeffPair p)) n ∈ ball c r := by
    simp only [map_zero]
    rw [canonicalPeriodicMidpoint_zero hp hp1 n]
    exact hmid
  rw [circleIntegral_sourceStandardRoot_inv_zeroGap hp hp1 0 n c r hgap hmid']
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  simp [I_sq]

/-- The off-diagonal free psi contour vanishes if the filled circle
avoids the other index's gap. -/
theorem sourcePsiFreeContour_off_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r)
    (hcircle : sphere c r ⊆ sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p))
    (havoid : closedBall c r ⊆
      (sourcePeriodicSegment hp hp1 (0 : CoeffPair p) n)ᶜ) :
    sourcePsiFreeContour hp hp1 n c r = 0 := by
  rw [sourcePsiFreeContour_eq_standardRoot_integral hp hp1 n c r hr hcircle,
    circleIntegral_sourceStandardRoot_inv_eq_zero hp hp1 0 n c r hr havoid]
  simp

/-- At zero potential each periodic gap is just its free lattice point. -/
theorem sourcePeriodicSegment_zero_source
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourcePeriodicSegment hp hp1 (0 : CoeffPair p) n =
      {(Real.pi : ℂ)*n} := by
  unfold sourcePeriodicSegment
  simp only [map_zero, canonicalPeriodicLeft_zero,
    canonicalPeriodicRight_zero, segment_same]

/-- Every circle of radius strictly between zero and pi around a free
center gives the Kronecker orthogonality in (2.21). -/
theorem sourcePsiFreeContour_orthogonality
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m n : ℤ) (r : ℝ)
    (hr : 0 < r) (hrπ : r < Real.pi) :
    sourcePsiFreeContour hp hp1 n ((Real.pi : ℂ)*m) r =
      if m = n then 1 else 0 := by
  let c : ℂ := (Real.pi : ℂ)*m
  have hcircle : sphere c r ⊆
      sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p) := by
    intro z hz k
    rw [sourcePeriodicSegment_zero_source hp hp1 k]
    intro hzk
    have heq : z = (Real.pi : ℂ)*k := Set.mem_singleton_iff.mp hzk
    have hzero : -2*sin z = 0 := by
      rw [heq]
      have hs : sin ((Real.pi : ℂ)*k) = 0 := by
        rw [mul_comm]
        exact Complex.sin_int_mul_pi k
      rw [hs]
      ring
    have hcenter := free_derivative_zero_eq_center hrπ m
      (sphere_subset_closedBall hz) hzero
    have hdist : r = 0 := by
      have h := mem_sphere.mp hz
      rw [hcenter, dist_self] at h
      exact h.symm
    exact (ne_of_gt hr) hdist
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl]
    exact sourcePsiFreeContour_diagonal hp hp1 m c r hr.le hcircle
      (mem_ball_self hr)
  · rw [if_neg hmn]
    apply sourcePsiFreeContour_off_diagonal hp hp1 n c r hr.le hcircle
    intro z hz hzn
    rw [sourcePeriodicSegment_zero_source hp hp1 n] at hzn
    have heq : z = (Real.pi : ℂ)*n := Set.mem_singleton_iff.mp hzn
    have hzero : -2*sin z = 0 := by
      rw [heq]
      have hs : sin ((Real.pi : ℂ)*n) = 0 := by
        rw [mul_comm]
        exact Complex.sin_int_mul_pi n
      rw [hs]
      ring
    have hcenter := free_derivative_zero_eq_center hrπ m hz hzero
    have heqmn : n = m := by
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hcast : (n : ℂ) = m := mul_left_cancel₀ hπ (heq.symm.trans hcenter)
      exact_mod_cast hcast
    exact hmn heqmn.symm

end NLS.ZakharovShabat
