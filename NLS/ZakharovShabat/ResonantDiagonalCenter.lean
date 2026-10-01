import NLS.ZakharovShabat.ResonantCauchyGap
import NLS.ZakharovShabat.ResonantConjugation
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The center selected by the actual resonant diagonal

The equation `ζ = nπ + a_n(ζ)` has exactly one solution in the full
resonant strip under the proved distant-strip bounds. A contraction on
a closed disc constructs the solution. This center is not assumed to
be the periodic midpoint. It is the parameter at which the common
diagonal of the reduced spectral matrix vanishes.
-/

noncomputable section
open Set Metric
open scoped NNReal
namespace NLS.ZakharovShabat

/-- The small diagonal gives an actual unique center in the full strip,
with the sharper displacement bound inherited from its fixed equation. -/
theorem exists_unique_resonantDiagonalCenter (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32) :
    ∃ ζ : ℂ, ζ ∈ refinedResonantDisk n ∧
      ‖ζ-(Real.pi : ℂ)*n‖ ≤ Real.pi/32 ∧
      ζ = (Real.pi : ℂ)*n + a ζ ∧
      ∀ z ∈ resonantStrip n, z = (Real.pi : ℂ)*n + a z → z = ζ := by
  let c : ℂ := (Real.pi : ℂ)*n
  let S : Set ℂ := closedBall c (Real.pi/8)
  have hS : S ⊆ refinedResonantDisk n := by
    intro z hz
    exact (mem_closedBall.mp hz).trans_lt (by linarith [Real.pi_pos])
  have hstrip : S ⊆ resonantStrip n := hS.trans (refinedResonantDisk_subset_strip n)
  let f : S → S := fun z => ⟨c+a z, by
    apply mem_closedBall.mpr
    simpa only [dist_eq_norm,add_sub_cancel_left] using
      (hb z (hstrip z.property)).trans (by linarith [Real.pi_pos])⟩
  have hf : ContractingWith (1/8 : ℝ≥0) f := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (c+a x.val) (c+a y.val) ≤ (1/8 : ℝ)*dist x.val y.val
    simpa only [dist_eq_norm,add_sub_add_left_eq_sub] using
      norm_diagonal_sub_le_on_refined_disk n a ha hb x y (hS x.property) (hS y.property)
  let : Nonempty S := ⟨⟨c,mem_closedBall_self (by positivity)⟩⟩
  let : CompleteSpace S := (isClosed_closedBall : IsClosed S).completeSpace_coe
  let ζ : ℂ := (hf.fixedPoint f).val
  have hζS : ζ ∈ S := (hf.fixedPoint f).property
  have hζ : ζ = c+a ζ := (congrArg Subtype.val hf.fixedPoint_isFixedPt).symm
  have hsmall : ‖ζ-c‖ ≤ Real.pi/32 := by
    rw [hζ,add_sub_cancel_left]
    exact hb ζ (hstrip hζS)
  refine ⟨ζ,hS hζS,hsmall,hζ,?_⟩
  intro z hz heq
  have hzS : z ∈ S := by
    apply mem_closedBall.mpr
    rw [dist_eq_norm,heq,add_sub_cancel_left]
    exact (hb z hz).trans (by linarith [Real.pi_pos])
  have hfix : Function.IsFixedPt f ⟨z,hzS⟩ := by
    apply Subtype.ext
    exact heq.symm
  exact congrArg Subtype.val (hf.fixedPoint_unique hfix)

/-- Comparing two center equations only requires the change of the
diagonal at one fixed spectral parameter. The contraction absorbs
the change of the moving parameter. -/
theorem norm_resonantDiagonalCenters_sub_le (n : ℤ) (a b : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (x y : ℂ) (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n)
    (hfixx : x = (Real.pi : ℂ)*n+a x)
    (hfixy : y = (Real.pi : ℂ)*n+b y) :
    ‖x-y‖ ≤ (8/7 : ℝ)*‖a y-b y‖ := by
  have hsplit : x-y = (a x-a y)+(a y-b y) := by
    calc
      x-y = ((Real.pi : ℂ)*n+a x)-((Real.pi : ℂ)*n+b y) := congrArg₂ (fun u v => u-v) hfixx hfixy
      _ = _ := by ring
  have htri : ‖x-y‖ ≤ (1/8 : ℝ)*‖x-y‖+‖a y-b y‖ := by
    calc
      _ = ‖(a x-a y)+(a y-b y)‖ := congrArg norm hsplit
      _ ≤ ‖a x-a y‖+‖a y-b y‖ := norm_add_le _ _
      _ ≤ _ := add_le_add
        (norm_diagonal_sub_le_on_refined_disk n a ha hb x y hx hy) le_rfl
  linarith

/-- The diagonal residual has a nonzero derivative at its constructed
center, including at a collapsed periodic gap. -/
theorem deriv_resonantDiagonalResidual_ne_zero (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (ζ : ℂ) (hζ : ζ ∈ refinedResonantDisk n) :
    deriv (fun z => z-(Real.pi : ℂ)*n-a z) ζ ≠ 0 := by
  have hder := (hasDerivAt_id ζ).sub_const ((Real.pi : ℂ)*n) |>.sub
    (ha ζ (refinedResonantDisk_subset_strip n hζ)).differentiableAt.hasDerivAt
  change HasDerivAt (fun z => z-(Real.pi : ℂ)*n-a z) (1-deriv a ζ) ζ at hder
  rw [hder.deriv]
  intro hzero
  have heq : deriv a ζ = 1 := (sub_eq_zero.mp hzero).symm
  have hbound := norm_deriv_le_on_refined_disk n a ha hb ζ hζ
  rw [heq,norm_one] at hbound
  norm_num at hbound

/-- Conjugation symmetry forces the unique diagonal center to be real. -/
theorem resonantDiagonalCenter_im_eq_zero (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (hconj : ∀ z ∈ resonantStrip n, a ((starRingEnd ℂ) z) = (starRingEnd ℂ) (a z))
    (ζ : ℂ) (hζ : ζ ∈ resonantStrip n)
    (hfix : ζ = (Real.pi : ℂ)*n+a ζ) : ζ.im = 0 := by
  obtain ⟨μ,_,_,hμ,hunique⟩ := exists_unique_resonantDiagonalCenter n a ha hb
  have heq := hunique ζ hζ hfix
  have hstar : (starRingEnd ℂ) ζ = (Real.pi : ℂ)*n+a ((starRingEnd ℂ) ζ) := by
    simpa only [map_add,map_mul,Complex.conj_ofReal,map_intCast,hconj ζ hζ]
      using congrArg (starRingEnd ℂ) hfix
  have hreal : (starRingEnd ℂ) ζ = ζ :=
    (hunique _ (conj_mem_resonantStrip hζ) hstar).trans heq.symm
  have hi := congrArg Complex.im hreal
  simp only [Complex.conj_im] at hi
  linarith

end NLS.ZakharovShabat
