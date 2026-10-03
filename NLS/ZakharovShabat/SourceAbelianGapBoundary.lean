import NLS.ZakharovShabat.SourceAbelianGapVerticalLimit
import NLS.ZakharovShabat.SourceCriticalRootRatioGapInteriorBound
import NLS.ComplexAnalysis.SquareRootPrimitiveBoundary

/-! # Exact half-plane boundary values on real spectral gaps

For every signed index, the normalized primitive tends to the positive
arcosh profile from the upper half-plane and its negative from the lower
half-plane. The limits allow arbitrary approaches and include endpoints
and collapsed gaps. This is the real-source assertion of Lemma 19.1(v).
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complete upper/lower boundary formula of Lemma 19.1(v), for
all points of the closed gap, including collapsed gaps. -/
theorem sourceAbelianHalfPlanePrimitive_gap_boundary_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    Tendsto (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper)
      (𝓝[sourceAbelianHalfPlane upper] (x : ℂ))
      (𝓝 (if upper then (sourceRealGapArcoshProfile hp φ n x : ℂ)
        else -(sourceRealGapArcoshProfile hp φ n x : ℂ))) := by
  have hspec := sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n upper
  have hprofile := sourceRealGapArcoshProfile_spec hp hp1 φ hφ n
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  by_cases hl : x = (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  · have hz : (x : ℂ) = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n :=
      Complex.ext hl him.1.symm
    rw [hl,hprofile.2.1]
    simp only [ofReal_zero,neg_zero,ite_self]
    rw [← hl,hz]
    exact hspec.2.1
  by_cases hr : x = (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  · have hz : (x : ℂ) = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n :=
      Complex.ext hr him.2.symm
    rw [hr,hprofile.2.2.1]
    simp only [ofReal_zero,neg_zero,ite_self]
    rw [← hr,hz]
    exact hspec.2.2
  have hxi : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hl),lt_of_le_of_ne hx.2 hr⟩
  obtain ⟨ε,M,hε,hε1,hM,hbound⟩ := exists_sourceCriticalRootRatio_gapInterior_bound hp hp1 φ hφ n x hxi
  have hweighted (z : ℂ) (hz : z.im ≠ 0) (hzε : ‖z-(x:ℂ)‖ ≤ ε) :
      ‖(deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) *
        ((Real.sqrt (1*‖z-(x:ℂ)‖) : ℝ) : ℂ)‖ ≤ M := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),one_mul]
    have hs : Real.sqrt ‖z-(x:ℂ)‖ ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (hzε.trans hε1)
    exact (mul_le_mul (hbound z hz hzε) hs (Real.sqrt_nonneg _) hM.le).trans_eq (mul_one M)
  have hray := sourceAbelianHalfPlanePrimitive_gap_vertical_limit hp hp1 φ hφ n upper x hx
  cases upper
  · apply tendsto_primitive_lower_of_sqrt_bound _ _ _ _ 1 M ε (ofReal_im x)
      zero_lt_one hM.le hε
    · intro z hz
      exact hspec.1 z hz
    · intro z hz _ hzε
      exact hweighted z hz.ne hzε
    · have hn : Tendsto (fun y : ℝ => -y) (𝓝[>] (0:ℝ)) (𝓝[<] (0:ℝ)) := by
        simpa only [neg_zero] using (tendsto_neg_nhdsGT_neg (a := (0:ℝ)))
      exact hray.comp hn
  · exact tendsto_primitive_upper_of_sqrt_bound _ _ _ _ 1 M ε (ofReal_im x)
      zero_lt_one hM.le hε (fun z hz => hspec.1 z hz)
      (fun z hz _ hzε => hweighted z hz.ne' hzε) hray

/-- The global primitive has the same exact boundary values after
adding the signed index normalization `i n pi`. -/
theorem sourceAbelianPrimitive_gap_boundary_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    Tendsto (fun z : ℂ => sourceAbelianPrimitive hp hp1 φ hφ z+I*(Real.pi : ℂ)*n)
      (𝓝[sourceAbelianHalfPlane upper] (x : ℂ))
      (𝓝 (if upper then (sourceRealGapArcoshProfile hp φ n x : ℂ)
        else -(sourceRealGapArcoshProfile hp φ n x : ℂ))) := by
  apply (sourceAbelianHalfPlanePrimitive_gap_boundary_limit hp hp1 φ hφ n upper x hx).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [sourceAbelianPrimitive_eq_global hp hp1 φ hφ
      (sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ upper hz),
    sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ hφ upper hz]
  exact sourceAbelianHalfPlanePrimitive_eq_zeroIndex_add hp hp1 φ hφ n upper hz

end NLS.ZakharovShabat
