import NLS.ZakharovShabat.SourcePsiOriginalJacobianContour
import NLS.ZakharovShabat.SourcePsiCandidateContourVariation
import NLS.ZakharovShabat.SourcePsiCandidateVariationRealAxis
import NLS.ZakharovShabat.SourceGapFunctionalZeros
import NLS.SequenceSpaces.DeletedRealOperator

/-!
# Original Jacobian kernel directions and gap zeros

Every direction of the actual bounded root Jacobian is represented by
the contour of its entire numerator variation. A real kernel direction
therefore gives a zero in every retained gap, including collapsed gaps.
The real matrix entries split complex kernel directions into two real
ones. The full root input and original contour disks are retained.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full matrix row sums to the bounded Jacobian applied to the direction.
The omitted input term is zero, so this is also the source's deleted row sum. -/
theorem hasSum_sourcePsiOriginalJacobianRow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (h : DeletedCoeff p n) :
    HasSum (fun r : ℤ => sourcePsiOriginalJacobianEntry hp hp1 n m r a ψ*(h:Coeff p) r)
      ((sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ h:Coeff p) m) := by
  simpa only [HasSum,SummationFilter.unconditional,sourcePsiOriginalJacobianEntry,mul_comm] using
    Coeff.tendsto_deletedOperator_matrixSum hp n m
      (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ) h

/-- The contour formula holds for every direction of the actual bounded derivative. -/
theorem SourceLemma12_4Data.originalRootJacobian_apply_variation_contour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψW : ψ ∈ W)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n m : ℤ) (a : Coeff p)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) (h : DeletedCoeff p n) :
    (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ h:Coeff p) m =
      ((n-m:ℤ):ℂ) * (∮ z in C((P.center:ℂ),P.radius),
        sourcePsiCandidateVariation n a (h:Coeff p) z / sourceCanonicalRoot hp hp1 ψ z) := by
  let Q := sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ
  let L : DeletedCoeff p n →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL)
  have hf := (L.hasFDerivAt.comp _
    (H.originalRootJacobian_hasFDerivAt ψ hψW n (Coeff.deleteCoordinateTo n a))).comp
      a (Coeff.deleteCoordinateTo (p := p) n).hasFDerivAt
  have he : (fun b : Coeff p => L (sourcePsiOriginalEquation hp hp1 n
      (Coeff.deleteCoordinateTo n b) ψ)) =
      (fun b : Coeff p => sourcePsiEquationCoordinate hp hp1 n m b ψ (P.center:ℂ) P.radius) :=
    funext (fun b => H.originalEquation_fullInput ψ hψW n m b P)
  simp only [Function.comp_def] at hf
  rw [he] at hf
  obtain ⟨U,_,hU,hformula⟩ := exists_local_sourcePsiEquationCoordinate_fderiv_root_direction
    hp hp1 n m a ψ hreal (P.center:ℂ) P.radius P.radius_pos.le P.sphere_subset_rootDomain
  have hdel : Coeff.deleteCoordinateTo n (h:Coeff p) = h :=
    Subtype.ext ((Coeff.deleteCoordinate_eq_self_iff n _).mpr h.property)
  calc
    (Q h:Coeff p) m = ((L.comp Q).comp (Coeff.deleteCoordinateTo n)) (h:Coeff p) := by
      simp only [ContinuousLinearMap.comp_apply,hdel]
      rfl
    _ = (fderiv ℂ (fun b : Coeff p => sourcePsiEquationCoordinate hp hp1 n m b ψ
        (P.center:ℂ) P.radius) a) (h:Coeff p) := by rw [hf.fderiv]
    _ = _ := hformula a ψ hU (h:Coeff p)

/-- A kernel vector has zero variation period in every retained row. -/
theorem SourceLemma12_4Data.originalKernel_variation_contour_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψW : ψ ∈ W)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n m : ℤ) (hmn : m ≠ n) (a : Coeff p)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) (h : DeletedCoeff p n)
    (hker : sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ h = 0) :
    (∮ z in C((P.center:ℂ),P.radius),
      sourcePsiCandidateVariation n a (h:Coeff p) z / sourceCanonicalRoot hp hp1 ψ z) = 0 := by
  have he := H.originalRootJacobian_apply_variation_contour ψ hψW hreal n m a P h
  rw [hker] at he
  have hn : ((n-m:ℤ):ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn.symm
  exact (mul_eq_zero.mp (by simpa using he.symm)).resolve_left hn

/-- A real kernel vector supplies a zero in each original retained gap. -/
theorem SourceLemma12_4Data.originalRealKernel_gapZero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_4Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (a : Coeff p)
    (ha : ∀ k : ℤ, (a k).im = 0) (h : DeletedCoeff p n)
    (hr : ∀ k : ℤ, ((h:Coeff p) k).im = 0)
    (hker : sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ h = 0)
    (m : ℤ) (hmn : m ≠ n) :
    ∃ z ∈ sourcePeriodicSegment hp hp1 ψ m, sourcePsiCandidateVariation n a (h:Coeff p) z = 0 := by
  obtain ⟨d,r,hrpos,he⟩ := hD.discs m
  let P := hD.periodCircle ψ hψV m d r hrpos he
  apply P.localNumerator_zero_of_circle hreal _
    ((analyticOnNhd_sourcePsiCandidateVariation hp hp1 n a (h:Coeff p)).mono (subset_univ _))
  · intro z hz
    have hzIm := sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal m z hz
    have hzre : (z.re:ℂ) = z := Complex.ext (by simp) (by simpa using hzIm.symm)
    rw [← hzre]
    apply sourcePsiCandidateVariation_im_eq_zero_of_real_data hp hp1 n a (h:Coeff p) _ hr
    intro k
    simp [displacedRoots,ha]
  · exact H.originalKernel_variation_contour_zero ψ hψW hreal n m hmn a P h hker

/-- Both real components of a complex kernel vector remain in the original kernel. -/
theorem SourceLemma12_4Data.originalKernel_realImag
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψW : ψ ∈ W)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (a : Coeff p)
    (ha : ∀ k : ℤ, (a k).im = 0) (h : DeletedCoeff p n)
    (hker : sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ h = 0) :
    sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ (DeletedCoeff.realPart h) = 0 ∧
    sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ (DeletedCoeff.imagPart h) = 0 :=
  Coeff.deletedOperator_kernel_realImag_of_real_entries hp n _
    (fun m k => H.originalJacobianEntry_real ψ hψW hreal n m k a ha) h hker

end NLS.ZakharovShabat
