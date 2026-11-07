import NLS.KdV.HillPrimitiveMomentsPhysical
import NLS.ZakharovShabat.SourceStandardRootOriginalLocalPeriod
import NLS.ZakharovShabat.SourceFullAbelianSquare

/-! Positive even centered moments vanish at every ACTUAL collapsed
selected gap, including the diagonal row. The filled primitive square
cancels the possible simple pole of the normalized differential. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

theorem centeredMoment_eq_zero_of_selected_gap_zero (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (d : ℕ) (hd : 0<d) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C)
    (hg : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (P.sourcePsi q))
      (periodOnePotential_mem _) (m:ℤ)=0) : P.centeredMoment W n m d q=0 := by
  let ψ := P.sourcePsi q
  let D := P.isolating.periodCircle ψ (P.image q hq.1).2 (m:ℤ)
    (P.centers (m:ℤ)) (P.radii (m:ℤ)) (P.radii_pos _) (P.discs_eq _)
  let τ := sourceStandardRootMidpoint (by simp) (by norm_num) ψ (m:ℤ)
  let A : ℂ → ℂ := fun z => (sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (z,ψ))^d*
    P.abelianGapNumerator n m (z,q)
  have hsq : AnalyticOnNhd ℂ (fun z => sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (z,ψ))
      (closedBall (P.centers (m:ℤ):ℂ) (P.radii (m:ℤ))) := by
    intro z hz
    exact C.fullSquare_analytic (m:ℤ) ψ hq.2 z (fun j hj _ => D.closedBall_subset_omittedDomain hz j hj)
  have hA : AnalyticOnNhd ℂ A (closedBall (P.centers (m:ℤ):ℂ) (P.radii (m:ℤ))) := by
    intro z hz
    exact ((hsq z hz).pow d).mul
      ((P.analytic_abelianGapNumerator_on_patch n m (z,q) ⟨hz,hq.1⟩).comp
        (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const))
  have heq : canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem _) (m:ℤ)=
      canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem _) (m:ℤ) :=
    sub_eq_zero.mp hg
  have hτ : τ=canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem _) (m:ℤ) := by
    dsimp only [τ,sourceStandardRootMidpoint,canonicalPeriodicMidpoint]
    rw [heq]
    ring
  have hhalf : sourceStandardRootHalfGap (by simp) (by norm_num) ψ (m:ℤ)=0 := by
    change (_-_)/2=0
    rw [heq,sub_self,zero_div]
  have hsq0 : sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (τ,ψ)=0 := by
    apply C.fullSquare_endpoint (m:ℤ) ψ hq.2 τ
    rw [hτ]
    simp
  have hA0 : A τ=0 := by simp only [A,hsq0,zero_pow (Nat.ne_of_gt hd),zero_mul]
  rw [P.centeredMoment_eq_square_contour C n m d q hq]
  have he : (∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)),
      (sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (z,ψ))^d*
        P.abelianFrequencyDifferential n (z,q))=
      ∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)), A z/sourceStandardRoot (by simp) (by norm_num) ψ (m:ℤ) z := by
    apply circleIntegral.integral_congr (P.radii_pos (m:ℤ)).le
    intro z hz
    dsimp only
    rw [P.abelianFrequencyDifferential_eq_gap_quotient n m (z,q) (D.sphere_subset_rootDomain hz)]
    dsimp only [A]
    rw [mul_div_assoc]
  rw [he]
  have hp := D.standardRoot_local_circle_period A hA
  change (∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)), A z/sourceStandardRoot (by simp) (by norm_num) ψ (m:ℤ) z)=_ at hp
  rw [hp]
  simp only [hhalf,zero_mul,add_zero,show sourceStandardRootMidpoint (by simp) (by norm_num) ψ (m:ℤ)=τ from rfl,
    hA0,intervalIntegral.integral_zero,mul_zero]

/-- Collapse of the ACTUAL original Hill gap makes every positive even
moment vanish; no separate collapse assumption on the Miura source is needed. -/
theorem centeredMoment_eq_zero_of_original_gapSquare_zero (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (d : ℕ) (hd : 0<d) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C)
    (hr : IsRealPeriodOneHminusOne q) (hg : hillHminusCanonicalGapSquare m q=0) :
    P.centeredMoment W n m d q=0 := by
  let B := P.parent.parent.miuraBall.actionBall
  have hqB : q ∈ B.source := (P.parent.subset (P.subset hq.1)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hqB hr⟩
  have hs := hillHminusCanonicalGapSquare_eq_Miura_of_real q hr u B.shift (B.image q hqB) (B.outside q hqB) m
  rw [hg] at hs
  have hp : (hillMiuraDiracRight u.val (m:ℤ)-hillMiuraDiracLeft u.val (m:ℤ))*
      (hillMiuraDiracRight u.val (m:ℤ)+hillMiuraDiracLeft u.val (m:ℤ))=0 := sq_eq_zero_iff.mp hs.symm
  have hl := hillMiura_positive_gap_left_pos u (m:ℤ) (by exact_mod_cast m.pos)
  change 0 < (hillMiuraDiracLeft u.val (m:ℤ)).re at hl
  have horder := hillMiuraDiracPair_ordered u.val (m:ℤ)
  have hsum : hillMiuraDiracRight u.val (m:ℤ)+hillMiuraDiracLeft u.val (m:ℤ)≠0 := by
    intro hzero
    have he := congrArg Complex.re hzero
    simp only [add_re,zero_re] at he
    linarith
  apply P.centeredMoment_eq_zero_of_selected_gap_zero C n m d hd q hq
  exact (mul_eq_zero.mp hp).resolve_right hsum

theorem centeredMoment_eq_zero_of_original_action_zero (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (d : ℕ) (hd : 0<d) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C)
    (hr : IsRealPeriodOneHminusOne q) (ha : hillHminusCanonicalAction m q=0) :
    P.centeredMoment W n m d q=0 :=
  P.centeredMoment_eq_zero_of_original_gapSquare_zero C n m d hd q hq hr
    ((hillHminusCanonicalAction_eq_zero_iff_gapSquare_of_real q hr m).mp ha)

end NLS.KdV.HillProductEquationPatch
