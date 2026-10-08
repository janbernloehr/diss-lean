import NLS.ZakharovShabat.AppendixDSineProducts
import NLS.ZakharovShabat.SingleSpectralProductOrders
import NLS.ComplexAnalysis.IsolatedOrderStability

/-! # Exact multiplicities of arbitrary displaced-root products

Properness of the root sequence gives finite fibers and isolating discs,
even when roots coincide. Rouché stability passes the stabilized finite
cutoff orders to the entire product without a simplicity hypothesis.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All indices at which the displaced sequence takes a prescribed value. -/
def displacedRootIndices (a : Coeff p) (z : ℂ) : Finset ℤ :=
  (finite_displacedRoots_preimage_compact a {z} isCompact_singleton).toFinset

@[simp] theorem mem_displacedRootIndices (a : Coeff p) (z : ℂ) (n : ℤ) :
    n ∈ displacedRootIndices a z ↔ displacedRoots a n = z := by
  simp [displacedRootIndices]

/-- A closed disc excludes every distinct root value, even when the center is repeated. -/
theorem exists_displacedRoots_isolating_closedBall (a : Coeff p) (z : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ k : ℤ, displacedRoots a k ∈ closedBall z r →
      displacedRoots a k = z := by
  let S : Set ℂ := displacedRoots a '' {k | displacedRoots a k ≠ z}
  have hclosed : IsClosed S :=
    (isProperMap_displacedRoots a).isClosedMap _ (isClosed_discrete _)
  have hz : z ∈ Sᶜ := by
    rintro ⟨k,hk,heq⟩
    exact hk heq
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hclosed.isOpen_compl.mem_nhds hz)
  refine ⟨r,hr,fun k hk => ?_⟩
  by_contra hne
  exact hball hk ⟨k,hne,rfl⟩

/-- Once the cutoff includes the root fiber, its analytic order is that fiber's cardinality. -/
theorem eventually_singleSpectralPartialProduct_order_eq_card (a : Coeff p) (z : ℂ) :
    ∀ᶠ N : ℕ in atTop,
      analyticOrderAt (fun w => singleSpectralPartialProduct (displacedRoots a) w N) z =
        ((displacedRootIndices a z).card : ℕ∞) := by
  filter_upwards [Finset.tendsto_Icc_neg.eventually
    (eventually_ge_atTop (displacedRootIndices a z))] with N hN
  have he : (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun k => displacedRoots a k = z) =
      displacedRootIndices a z := by
    ext k
    simp only [Finset.mem_filter, mem_displacedRootIndices]
    exact ⟨fun hk => hk.2, fun hk => ⟨hN ((mem_displacedRootIndices a z k).mpr hk),hk⟩⟩
  rw [analyticOrderAt_singleSpectralPartialProduct]
  simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
    congrArg (fun s : Finset ℤ => (s.card : ℕ∞)) he

/-- The entire product has finite order at every point. -/
theorem analyticOrderAt_entireSingleSpectralProduct_displaced_ne_top (hp : p ≠ ⊤)
    (a : Coeff p) (z : ℂ) :
    analyticOrderAt (entireSingleSpectralProduct (displacedRoots a)) z ≠ ⊤ := by
  obtain ⟨r,hr,hiso⟩ := exists_displacedRoots_isolating_closedBall a z
  apply NLS.ComplexAnalysis.analyticOrderAt_ne_top_of_isolated _ z r hr
    ((analyticOnNhd_entireSingleSpectralProduct hp _ (memℓp_displacedRoots a)).mono (subset_univ _))
  intro w hw hw0
  obtain ⟨k,rfl⟩ := (jointSingleSpectralProduct_eq_zero_iff_of_lp hp a w).mp hw0
  exact hiso k hw

/-- The entire product counts every occurrence of a root, including arbitrary collisions. -/
theorem analyticOrderAt_entireSingleSpectralProduct_displaced (hp : p ≠ ⊤)
    (a : Coeff p) (z : ℂ) :
    analyticOrderAt (entireSingleSpectralProduct (displacedRoots a)) z =
      ((displacedRootIndices a z).card : ℕ∞) := by
  obtain ⟨r,hr,hiso⟩ := exists_displacedRoots_isolating_closedBall a z
  have hFz (N : ℕ) (w : ℂ) (hw : w ∈ closedBall z r)
      (hw0 : singleSpectralPartialProduct (displacedRoots a) w N = 0) : w = z := by
    by_contra hne
    exact singleSpectralPartialProduct_ne_zero (displacedRoots a) w
      (fun k hk => hne (hk ▸ hiso k (hk ▸ hw))) N hw0
  have hgz (w : ℂ) (hw : w ∈ closedBall z r)
      (hw0 : entireSingleSpectralProduct (displacedRoots a) w = 0) : w = z := by
    obtain ⟨k,rfl⟩ := (jointSingleSpectralProduct_eq_zero_iff_of_lp hp a w).mp hw0
    exact hiso k hw
  have hconv := tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp
    (displacedRoots a) (memℓp_displacedRoots a)
  have hstab := NLS.ComplexAnalysis.eventually_analyticOrderNatAt_eq_of_isolated _ _ z r hr
    (fun N => (analyticOnNhd_singleSpectralPartialProduct (displacedRoots a) N).mono (subset_univ _))
    ((analyticOnNhd_entireSingleSpectralProduct hp _ (memℓp_displacedRoots a)).mono (subset_univ _))
    hFz hgz
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere z r)).mp
      (hconv.mono (subset_univ _)))
  obtain ⟨N,hN,horder⟩ := (hstab.and (eventually_singleSpectralPartialProduct_order_eq_card a z)).exists
  have hn : analyticOrderNatAt (entireSingleSpectralProduct (displacedRoots a)) z =
      (displacedRootIndices a z).card := by
    rw [← hN]
    simpa only [analyticOrderNatAt, ENat.toNat_natCast] using congrArg ENat.toNat horder
  rw [← Nat.cast_analyticOrderNatAt
    (analyticOrderAt_entireSingleSpectralProduct_displaced_ne_top hp a z), hn]

/-- Appendix D's scalar normalization preserves the exact root multiplicity. -/
theorem analyticOrderAt_appendixDProduct (hp : p ≠ ⊤) (a : Coeff p) (z : ℂ) :
    analyticOrderAt (fun w => appendixDProduct (w,a)) z =
      ((displacedRootIndices a z).card : ℕ∞) := by
  change analyticOrderAt ((fun _ : ℂ => -(1/2:ℂ)) *
    entireSingleSpectralProduct (displacedRoots a)) z = _
  rw [analyticOrderAt_mul analyticAt_const
    ((analyticOnNhd_entireSingleSpectralProduct hp _ (memℓp_displacedRoots a)) z (mem_univ _)),
    show analyticOrderAt (fun _ : ℂ => -(1/2:ℂ)) z = 0 from
      analyticOrderAt_eq_zero.mpr (Or.inr (by norm_num)), zero_add,
    analyticOrderAt_entireSingleSpectralProduct_displaced hp a z]

end NLS.ZakharovShabat
