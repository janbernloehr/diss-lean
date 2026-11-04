import NLS.KdV.HillPairedDirichletInterpolation
import NLS.ComplexAnalysis.BoundedUniformMultiplier

/-! The actual normalized Hill numerator is the locally uniform
limit of its filled Dirichlet interpolation sums after quadratic
descent. Signed frequency residues are paired with their exact
derivative normalization; the central contribution cancels. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem finite_Hill_Dirichlet_interpolation_eq_weighted_auxiliary
    (P : HillProductEquationPatch) (n : ℕ+) (N : ℕ) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne q) (w : ℂ)
    (hw : auxiliaryPeriodOneCharacteristic (by norm_num) (by norm_num) .dirichlet (P.sourcePsi q) w ≠ 0) :
    (hillHminusDirichlet q (w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))/2)*
      ((∑ m ∈ Finset.Icc (-(N:ℤ)) N, hillAuxiliaryPsiInterpolationTerm ((n:ℕ):ℤ)
        (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2)
        (P.parent.parent.miuraBall.actionBall.lift q) m w)+
       (∑ m ∈ Finset.Icc (-(N:ℤ)) N, hillAuxiliaryPsiInterpolationTerm ((n:ℕ):ℤ)
        (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2)
        (P.parent.parent.miuraBall.actionBall.lift q) m (-w))) =
      ∑ j ∈ Finset.Icc (-(N:ℤ)) N, positiveScalarExtension (fun m : ℕ+ =>
        hillHminusPsiDirichletInterpolationTerm n m q (w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))) j := by
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  let a : Coeff 2 := P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q)
  let T := hillAuxiliaryPsiInterpolationTerm ((n:ℕ):ℤ) a u.val
  have hz : T 0 w+T 0 (-w)=0 := by
    dsimp only [T,hillAuxiliaryPsiInterpolationTerm]
    rw [hillMiuraDiracDirichlet_zero u]
    simp only [sub_zero,div_neg,add_neg_cancel]
  have hs := sum_symmetricCutoff_eq_central_add_positive_pairs (fun m => T m w+T m (-w)) N
  rw [hz,zero_add] at hs
  change (hillHminusDirichlet q (w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))/2)*
    ((∑ m ∈ Finset.Icc (-(N:ℤ)) N, T m w)+(∑ m ∈ Finset.Icc (-(N:ℤ)) N, T m (-w))) = _
  rw [← Finset.sum_add_distrib,hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← positiveScalarExtension_const_mul]
  apply congrArg (fun f : ℕ+ → ℂ => positiveScalarExtension f j)
  funext m
  exact P.weighted_auxiliary_interpolation_pair n m q hq hr w hw

theorem tendstoUniformlyOn_Hill_Dirichlet_interpolation
    (P : HillProductEquationPatch) (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne q) (S : Set ℂ) (hS : IsCompact S)
    (hzero : ∀ w ∈ S, auxiliaryPeriodOneCharacteristic (by norm_num) (by norm_num) .dirichlet (P.sourcePsi q) w ≠ 0) :
    TendstoUniformlyOn (fun N : ℕ => fun w : ℂ => ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
      positiveScalarExtension (fun m : ℕ+ => hillHminusPsiDirichletInterpolationTerm n m q
        (w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))) j)
      (fun w => hillHminusCanonicalPsi n (w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q)) atTop S := by
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  let a : Coeff 2 := P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q)
  let g := auxiliaryPeriodOneCharacteristic (by norm_num) (by norm_num) .dirichlet (hillMiuraDiagonal u.val)
  let c : ℂ := P.parent.parent.miuraBall.actionBall.shift
  obtain ⟨L₀,hL₀⟩ := hS.exists_bound_of_continuousOn (continuousOn_id : ContinuousOn (fun w : ℂ => w) S)
  let L := max 0 L₀
  have hL : 0 ≤ L := le_max_left _ _
  have hg : ∀ w ∈ S, g w ≠ 0 := hzero
  have hbound : ∀ w ∈ S, ‖w‖ ≤ L := fun w hw => (hL₀ w hw).trans (le_max_right _ _)
  have ht := tendstoUniformlyOn_hillAuxiliaryPsiInterpolation ((n:ℕ):ℤ) a u L hL
  have hpos := ht.mono (show S ⊆ {w | ‖w‖ ≤ L ∧ g w ≠ 0} from fun w hw => ⟨hbound w hw,hg w hw⟩)
  have hneg := (ht.comp (fun w : ℂ => -w)).mono (show S ⊆
      (fun w : ℂ => -w) ⁻¹' {w | ‖w‖ ≤ L ∧ g w ≠ 0} from by
    intro w hw
    refine ⟨by simpa only [norm_neg] using hbound w hw,?_⟩
    have he : g (-w) = -g w := auxiliaryDirichlet_hillMiuraDiagonal_neg u.val w
    rw [he]
    exact neg_ne_zero.mpr (hg w hw))
  have hsum := hpos.add hneg
  have hW : ContinuousOn (fun w : ℂ => hillHminusDirichlet q (w^2-c)/2) S := by
    intro w _
    exact (((analyticOnNhd_hillHminusDirichlet_energy q (w^2-c) (mem_univ _)).comp
      (f := fun z : ℂ => z^2-c) ((analyticAt_id.pow 2).sub analyticAt_const)).div_const).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hW
  have hMpos : 0 < max 1 M := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
  have hu := tendstoUniformlyOn_bounded_const_mul (c := fun w => hillHminusDirichlet q (w^2-c)/2)
    hsum (max 1 M) hMpos (fun w hw => (hM w hw).trans (le_max_right _ _))
  have hlimit (w : ℂ) (hw : w ∈ S) :
      (hillHminusDirichlet q (w^2-c)/2)*
        (sourcePsiCandidate ((n:ℕ):ℤ) (w,a)/g w+sourcePsiCandidate ((n:ℕ):ℤ) (-w,a)/g (-w)) =
      hillHminusCanonicalPsi n (w^2-c,q) := by
    have himage := P.parent.parent.miuraBall.actionBall.image q (P.parent.subset (P.subset hq)).1
    have hgw : g w=w*hillHminusDirichlet q (w^2-c) :=
      auxiliaryDirichlet_eq_mul_hillHminusDirichlet q u.val c w himage
    have hgn : g (-w) = -g w := auxiliaryDirichlet_hillMiuraDiagonal_neg u.val w
    have hwne : w ≠ 0 := by intro he; apply hg w hw; rw [hgw,he,zero_mul]
    have hSne : hillHminusDirichlet q (w^2-c) ≠ 0 := by intro he; apply hg w hw; rw [hgw,he,mul_zero]
    have hh := P.canonicalPsi_frequency_identity n q hq w
    have hnum : sourcePsiCandidate ((n:ℕ):ℤ) (w,a) = sourcePsiCandidate ((n:ℕ):ℤ) (-w,a)+
        2*w*hillHminusCanonicalPsi n (w^2-c,q) := by linear_combination -hh
    rw [hnum,hgn,hgw]
    field_simp [hwne,hSne]
    ring
  apply (hu.congr (Eventually.of_forall (fun N w hw =>
    P.finite_Hill_Dirichlet_interpolation_eq_weighted_auxiliary n N q hq hr w (hzero w hw)))).congr_right
  exact hlimit

end NLS.KdV.HillProductEquationPatch
