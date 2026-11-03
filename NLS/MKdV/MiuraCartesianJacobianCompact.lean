import NLS.MKdV.MiuraCartesianWeightedNormalization
import NLS.SequenceSpaces.CompactSymbolProduct
import NLS.ZakharovShabat.SourceBirkhoffJacobianCompact

/-! # Compact remainder of the actual Cartesian Jacobian

At every physical real L2 source the full Cartesian derivative differs
from its free bounded equivalence by a compact operator. Root derivatives
are controlled in the bounded-sequence norm; multiplication by the fixed
NLS coordinate sequence makes their contribution compact.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem analyticAt_miuraCartesianRootSequence (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    AnalyticAt ℂ miuraCartesianRootSequence a := by
  let φ : realDiagonalSourceLocus 2 := ⟨scalarL2Diagonal a,scalarL2Diagonal_realDiagonal a ha⟩
  obtain ⟨U,_,hφU,hA,_⟩ := exists_local_sourceDiagonalActionRootSequence_analytic φ
  have h : AnalyticAt ℂ sourceDiagonalActionRootSequence (scalarL2Diagonal a) := hA φ.val hφU
  exact h.comp (scalarL2Diagonal.analyticAt a)

theorem hasFDerivAt_miuraNLSCoordinateSequence (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    HasFDerivAt miuraNLSCoordinateSequence
      ((sourceBirkhoffJacobian (by simp) (by norm_num) miuraActionFlowFamily.psi
        (scalarL2Diagonal a)).comp scalarL2Diagonal) a := by
  let D := miuraActionFlowFamily.data
  have hφ := (scalarL2Diagonal_realDiagonal a ha).1
  exact (D.analytic _ (D.real_subset hφ)).differentiableAt.hasFDerivAt.comp a scalarL2Diagonal.hasFDerivAt

theorem isCompactOperator_fderiv_miuraNLSCoordinateSequence_sub_free (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    IsCompactOperator (fderiv ℂ miuraNLSCoordinateSequence a-fderiv ℂ miuraNLSCoordinateSequence 0) := by
  let φ : realTypeSourceSubmodule 2 := ⟨scalarL2Diagonal a,(scalarL2Diagonal_realDiagonal a ha).1⟩
  have hc := (miuraActionFlowFamily.data.isCompactOperator_jacobianRemainder_real φ).comp_clm scalarL2Diagonal
  have h0 : fderiv ℂ miuraNLSCoordinateSequence 0 = (sourceBirkhoffFourier (p := 2)).comp scalarL2Diagonal :=
    hasFDerivAt_miuraNLSCoordinates_zero.fderiv
  rw [(hasFDerivAt_miuraNLSCoordinateSequence a ha).fderiv,h0]
  exact hc

theorem isCompactOperator_miuraCartesianRootSequence_sub_free (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    IsCompactOperator (Coeff.multiplierCLM (p := 2)
      (miuraCartesianRootSequence a-miuraCartesianRootSequence 0)) := by
  let φ : realDiagonalSourceLocus 2 := ⟨scalarL2Diagonal a,scalarL2Diagonal_realDiagonal a ha⟩
  have h := isCompactOperator_sourceDiagonalActionRootSequence_sub_free φ 2
  simpa only [miuraCartesianRootSequence,map_zero] using h

theorem isCompactOperator_fderiv_miuraNLSCoordinate_component_sub_free
    (L : (Coeff 2 × Coeff 2) →L[ℂ] Coeff 2) (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    IsCompactOperator (fderiv ℂ (fun b => L (miuraNLSCoordinateSequence b)) a-
      fderiv ℂ (fun b => L (miuraNLSCoordinateSequence b)) 0) := by
  have hzero : ∀ j : ℤ, (0 : Coeff 2) j = conj ((0 : Coeff 2) (-j)) := by intro j; simp
  have hF := L.hasFDerivAt.comp a (hasFDerivAt_miuraNLSCoordinateSequence a ha).differentiableAt.hasFDerivAt
  have hF₀ := L.hasFDerivAt.comp 0 (hasFDerivAt_miuraNLSCoordinateSequence 0 hzero).differentiableAt.hasFDerivAt
  change HasFDerivAt (fun b => L (miuraNLSCoordinateSequence b)) _ a at hF
  change HasFDerivAt (fun b => L (miuraNLSCoordinateSequence b)) _ 0 at hF₀
  rw [hF.fderiv,hF₀.fderiv,← ContinuousLinearMap.comp_sub]
  exact (isCompactOperator_fderiv_miuraNLSCoordinateSequence_sub_free a ha).clm_comp L

theorem miuraNLSCoordinateSequence_zero : miuraNLSCoordinateSequence 0 = 0 := by
  rw [miuraNLSCoordinateSequence,map_zero,miuraActionFlowFamily.data.birkhoff_map_zero]

theorem isCompactOperator_fderiv_miuraScaledNLSCoordinate_sub_free
    (L : (Coeff 2 × Coeff 2) →L[ℂ] Coeff 2) (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    IsCompactOperator
      (fderiv ℂ (fun b => Coeff.multiplier (miuraCartesianRootSequence b) (L (miuraNLSCoordinateSequence b))) a-
        fderiv ℂ (fun b => Coeff.multiplier (miuraCartesianRootSequence b) (L (miuraNLSCoordinateSequence b))) 0) := by
  have hzero : ∀ j : ℤ, (0 : Coeff 2) j = conj ((0 : Coeff 2) (-j)) := by intro j; simp
  exact Coeff.isCompactOperator_fderiv_multiplier_sub_zero (by simp) miuraCartesianRootSequence
    (fun b => L (miuraNLSCoordinateSequence b)) a
    (analyticAt_miuraCartesianRootSequence a ha).differentiableAt
    (L.differentiableAt.comp a (hasFDerivAt_miuraNLSCoordinateSequence a ha).differentiableAt)
    (analyticAt_miuraCartesianRootSequence 0 hzero).differentiableAt
    (L.differentiableAt.comp 0 (hasFDerivAt_miuraNLSCoordinateSequence 0 hzero).differentiableAt)
    (by rw [miuraNLSCoordinateSequence_zero,map_zero])
    (isCompactOperator_fderiv_miuraNLSCoordinate_component_sub_free L a ha)
    (isCompactOperator_miuraCartesianRootSequence_sub_free a ha)

def miuraScaledNLSCoordinateX (a : Coeff 2) : Coeff 2 :=
  Coeff.multiplier (miuraCartesianRootSequence a) (miuraNLSCoordinateSequence a).1

def miuraScaledNLSCoordinateY (a : Coeff 2) : Coeff 2 :=
  Coeff.multiplier (miuraCartesianRootSequence a) (miuraNLSCoordinateSequence a).2

theorem differentiableAt_miuraScaledNLSCoordinate
    (L : (Coeff 2 × Coeff 2) →L[ℂ] Coeff 2) (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    DifferentiableAt ℂ
      (fun b => Coeff.multiplier (miuraCartesianRootSequence b) (L (miuraNLSCoordinateSequence b))) a := by
  exact (((Coeff.multiplierBilinear (p := 2)).differentiableAt.comp a
    (analyticAt_miuraCartesianRootSequence a ha).differentiableAt).clm_apply
      (L.differentiableAt.comp a (hasFDerivAt_miuraNLSCoordinateSequence a ha).differentiableAt))

theorem fderiv_miuraScaledNLSCartesianMap (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    fderiv ℂ miuraScaledNLSCartesianMap a =
      ((fderiv ℂ miuraScaledNLSCoordinateX a).prod (-(fderiv ℂ miuraScaledNLSCoordinateY a))).prod
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0) := by
  have hx : DifferentiableAt ℂ miuraScaledNLSCoordinateX a :=
    differentiableAt_miuraScaledNLSCoordinate (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)) a ha
  have hy : DifferentiableAt ℂ miuraScaledNLSCoordinateY a :=
    differentiableAt_miuraScaledNLSCoordinate (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2)) a ha
  have hd := (hx.hasFDerivAt.prodMk hy.hasFDerivAt.neg).prodMk
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).hasFDerivAt
  change HasFDerivAt miuraScaledNLSCartesianMap _ a at hd
  exact hd.fderiv

theorem isCompactOperator_fderiv_miuraScaledNLSCartesianMap_sub_free (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    IsCompactOperator (fderiv ℂ miuraScaledNLSCartesianMap a-fderiv ℂ miuraScaledNLSCartesianMap 0) := by
  have hzero : ∀ j : ℤ, (0 : Coeff 2) j = conj ((0 : Coeff 2) (-j)) := by intro j; simp
  have hx : IsCompactOperator (fderiv ℂ miuraScaledNLSCoordinateX a-fderiv ℂ miuraScaledNLSCoordinateX 0) :=
    isCompactOperator_fderiv_miuraScaledNLSCoordinate_sub_free (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)) a ha
  have hy : IsCompactOperator (fderiv ℂ miuraScaledNLSCoordinateY a-fderiv ℂ miuraScaledNLSCoordinateY 0) :=
    isCompactOperator_fderiv_miuraScaledNLSCoordinate_sub_free (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2)) a ha
  have hxy := Coeff.isCompactOperator_prodCLM
    (fderiv ℂ miuraScaledNLSCoordinateX a-fderiv ℂ miuraScaledNLSCoordinateX 0)
    (-(fderiv ℂ miuraScaledNLSCoordinateY a-fderiv ℂ miuraScaledNLSCoordinateY 0)) hx hy.neg
  have hc := Coeff.isCompactOperator_prodCLM
    ((fderiv ℂ miuraScaledNLSCoordinateX a-fderiv ℂ miuraScaledNLSCoordinateX 0).prod
      (-(fderiv ℂ miuraScaledNLSCoordinateY a-fderiv ℂ miuraScaledNLSCoordinateY 0)))
    (0 : Coeff 2 →L[ℂ] ℂ) hxy isCompactOperator_zero
  have he : fderiv ℂ miuraScaledNLSCartesianMap a-fderiv ℂ miuraScaledNLSCartesianMap 0 =
      ((fderiv ℂ miuraScaledNLSCoordinateX a-fderiv ℂ miuraScaledNLSCoordinateX 0).prod
        (-(fderiv ℂ miuraScaledNLSCoordinateY a-fderiv ℂ miuraScaledNLSCoordinateY 0))).prod 0 := by
    rw [fderiv_miuraScaledNLSCartesianMap a ha,fderiv_miuraScaledNLSCartesianMap 0 hzero]
    apply ContinuousLinearMap.ext
    intro h
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · change -(fderiv ℂ miuraScaledNLSCoordinateY a h)-
          -(fderiv ℂ miuraScaledNLSCoordinateY 0 h) =
            -((fderiv ℂ miuraScaledNLSCoordinateY a h)-(fderiv ℂ miuraScaledNLSCoordinateY 0 h))
        abel
    · exact sub_self _
  rw [he]
  exact hc

theorem miuraCartesianNormalization_fderiv (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    miuraCartesianNormalization.comp (fderiv ℂ miuraPositiveCartesianMap a) =
      fderiv ℂ miuraScaledNLSCartesianMap a := by
  have hd := miuraCartesianNormalization.hasFDerivAt.comp a
    (analyticAt_miuraPositiveCartesianMap a ha).differentiableAt.hasFDerivAt
  change HasFDerivAt (fun b => miuraCartesianNormalization (miuraPositiveCartesianMap b)) _ a at hd
  exact hd.fderiv.symm.trans (miuraCartesianNormalization_map_eventually a ha).fderiv_eq

/-- The full complex derivative at every physical real source is a
compact perturbation of the actual free bounded Cartesian equivalence. -/
theorem isCompactOperator_miuraCartesianJacobian_sub_free (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    IsCompactOperator (fderiv ℂ miuraPositiveCartesianMap a-miuraCartesianFreeJacobian) := by
  have hzero : ∀ j : ℤ, (0 : Coeff 2) j = conj ((0 : Coeff 2) (-j)) := by intro j; simp
  let T := fderiv ℂ miuraPositiveCartesianMap a-miuraCartesianFreeJacobian
  have hn : IsCompactOperator (miuraCartesianNormalization.comp T) := by
    change IsCompactOperator (miuraCartesianNormalization.comp
      (fderiv ℂ miuraPositiveCartesianMap a-fderiv ℂ miuraPositiveCartesianMap 0))
    rw [ContinuousLinearMap.comp_sub,miuraCartesianNormalization_fderiv a ha,
      miuraCartesianNormalization_fderiv 0 hzero]
    exact isCompactOperator_fderiv_miuraScaledNLSCartesianMap_sub_free a ha
  have he : miuraCartesianDenormalization.comp (miuraCartesianNormalization.comp T) = T := by
    apply ContinuousLinearMap.ext
    intro h
    exact miuraCartesianDenormalization_normalization (T h)
  change IsCompactOperator T
  rw [← he]
  exact hn.clm_comp miuraCartesianDenormalization

end NLS.MKdV
