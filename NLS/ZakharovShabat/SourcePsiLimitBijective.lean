import NLS.ZakharovShabat.SourcePsiLimitRealKernelUniqueness
import NLS.ZakharovShabat.SourcePsiContourConjugation
import NLS.SequenceSpaces.RealOperator

/-!
# Pointwise bijectivity of the actual psi limit operator

Real-centered contours give real matrix entries. Every complex kernel
direction therefore splits into two real kernel directions, both of
which vanish by full-product interpolation. The compact correction to
`2I` then supplies bijectivity on the same norm-limit operator.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual scalar limit matrix entry is real on a real-centered
circle for real-type data and gap-contained roots. -/
theorem sourcePsiLimitMatrixEntry_im_eq_zero_of_realCenteredCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (m k : ℤ) (x R : ℝ) (hR : 0 < R)
    (hcircle : sphere (x:ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    (sourcePsiLimitMatrixEntry hp hp1 m k a φ (x:ℂ) R).im = 0 := by
  have hroots (j : ℤ) : (displacedRoots a j).im = 0 :=
    sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ hφ j _ (ha j)
  have hintegrand : EqOn (sourcePsiLimitMatrixIntegrand hp hp1 m k a φ)
      (fun z => sourcePsiContourIntegrandJoint hp hp1 k (z,(a,φ)))
      (sphere (x:ℂ) R) := by
    intro z hz
    have hzk : z ≠ displacedRoots a k := by
      intro heq
      exact (hcircle hz k) (heq.symm ▸ ha k)
    rw [sourcePsiLimitMatrixIntegrand_eq_fullProductVariation_single
      hp hp1 m k a φ z (hcircle hz) hzk,
      sourcePsiFullProductVariation_single hp hp1]
    simp [sourcePsiContourIntegrandJoint,div_eq_mul_inv]
  have hJ : (∮ z in C((x:ℂ),R),
      sourcePsiContourIntegrandJoint hp hp1 k (z,(a,φ))).im = 0 :=
    NLS.ComplexAnalysis.circleIntegral_im_eq_zero_of_anti_conj
      (fun z => sourcePsiContourIntegrandJoint hp hp1 k (z,(a,φ))) x R hR
      (fun z hz => sourcePsiContourIntegrandJoint_conj_of_real_data
        hp hp1 φ hφ k a hroots z (hcircle hz))
  unfold sourcePsiLimitMatrixEntry
  rw [circleIntegral.integral_congr hR.le hintegrand]
  simp [Complex.div_im,hJ]

/-- Reality holds for every basis entry of any bounded operator with
the actual limit contours and real centers. -/
theorem sourcePsiLimitMatrixOperator_real_matrix_entries
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (c : ℤ → ℂ) (R : ℤ → ℝ) (hcenter : ∀ m : ℤ, (c m).im = 0)
    (hR : ∀ m : ℤ, 0 < R m)
    (hcircle : ∀ m : ℤ, sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (Qstar : Coeff p →L[ℂ] Coeff p)
    (hentry : ∀ m k : ℤ, (Qstar (lp.single p k 1)) m =
      sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) :
    ∀ m k : ℤ, ((Qstar (lp.single p k 1)) m).im = 0 := by
  intro m k
  obtain ⟨x,hx⟩ : ∃ x : ℝ, c m = (x:ℂ) := by
    exact ⟨(c m).re,Complex.ext (by simp) (by simp [hcenter m])⟩
  rw [hentry,hx]
  apply sourcePsiLimitMatrixEntry_im_eq_zero_of_realCenteredCircle
    hp hp1 a φ hφ ha m k x (R m) (hR m)
  simpa only [← hx] using hcircle m

/-- The real-kernel uniqueness theorem implies full complex
injectivity for the actual bounded contour-limit operator. -/
theorem sourcePsiLimitMatrixOperator_injective
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (c : ℤ → ℂ) (R : ℤ → ℝ) (hcenter : ∀ m : ℤ, (c m).im = 0)
    (hgeom : ∀ m : ℤ,
      0 < R m ∧ sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
      closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m ∧
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (Qstar : Coeff p →L[ℂ] Coeff p)
    (hentry : ∀ m k : ℤ, (Qstar (lp.single p k 1)) m =
      sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) :
    Function.Injective Qstar := by
  apply Coeff.operator_injective_of_realKernelZero hp Qstar
    (sourcePsiLimitMatrixOperator_real_matrix_entries hp hp1 a φ hφ ha c R
      hcenter (fun m => (hgeom m).1) (fun m => (hgeom m).2.2.2) Qstar hentry)
  exact sourcePsiLimitMatrixOperator_realKernel_eq_zero
    hp hp1 a φ hφ ha c R hcenter hgeom Qstar hentry

/-- For every fixed real-type potential and full gap-contained root
vector, the actual fixed-root norm limit is bijective. All conclusions
use one common real-centered contour family and one operator. -/
theorem exists_sourcePsiLimitMatrixOperator_normLimit_bijective
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ, (c m).im = 0) ∧
      (∀ m : ℤ,
        0 < R m ∧ sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ) ∧
      ∃ Qstar : Coeff p →L[ℂ] Coeff p,
        (∀ m k : ℤ, (Qstar (lp.single p k 1)) m =
          sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) ∧
        Tendsto (fun n : ℤ => sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ)
          (Filter.comap Int.natAbs Filter.atTop) (𝓝 Qstar) ∧
        IsCompactOperator (Qstar - (2:ℂ) • ContinuousLinearMap.id ℂ (Coeff p)) ∧
        Function.Bijective Qstar := by
  obtain ⟨c,R,hcenter,hgeom,Qstar,hentry,hlimit,hcompact,_⟩ :=
    exists_sourcePsiLimitMatrixOperator_normLimit_realKernelZero hp hp1 a φ hφ ha
  refine ⟨c,R,hcenter,hgeom,Qstar,hentry,hlimit,hcompact,?_⟩
  exact NLS.CompactSpectrum.bijective_of_injective_compact_sub_smul
    Qstar (by norm_num : (2:ℂ) ≠ 0) hcompact
    (sourcePsiLimitMatrixOperator_injective hp hp1 a φ hφ ha
      c R hcenter hgeom Qstar hentry)

end NLS.ZakharovShabat
