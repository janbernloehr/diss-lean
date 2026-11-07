import NLS.KdV.HillCubicContourReflection
import NLS.KdV.HillCubicPrimitiveMomentReduction
import NLS.KdV.HillPrimitiveMomentSeriesNeighborhood
import NLS.ZakharovShabat.SourceFiniteGapContourDecomposition

/-! The actual finite-gap outer cubic Hill contour equals its positive
second-moment series, with exact central and reflection factors. Physical
Hamiltonian differentiation is a separate obligation. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

theorem filledCubic_circle_eq_zero_of_gap_zero (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n : ℕ+) (m : ℤ) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) (hr : IsRealPeriodOneHminusOne q)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (P.sourcePsi q))
      (periodOnePotential_mem _) (n:ℤ) ≠ 0)
    (hm : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (P.sourcePsi q))
      (periodOnePotential_mem _) m = 0) :
    (∮ z in C((P.centers m:ℂ),P.radii m), P.filledCubicFrequencyIntegrand W n (z,q))=0 := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 m
    (P.centers m) (P.radii m) (P.radii_pos _) (P.discs_eq _)
  have hd : DifferentiableOn ℂ (fun z => P.filledCubicFrequencyIntegrand W n (z,q))
      (closedBall (P.centers m:ℂ) (P.radii m)) := by
    intro z hz
    apply (P.analytic_filledCubicFrequencyIntegrand C n q hq hr hn z ?_).differentiableAt.differentiableWithinAt
    intro j hj
    exact D.closedBall_subset_omittedDomain hz j (fun he => hj (he ▸ hm))
  exact (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero (P.radii_pos m).le

theorem filledCubic_positive_circle_reduction (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) :
    (4/(I*(Real.pi:ℂ))) *
      (∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)), P.filledCubicFrequencyIntegrand W n (z,q)) =
      (2*(Real.pi:ℂ)*(n:ℤ))^3*(if m=n then 1 else 0)-12*(m:ℤ)*P.centeredMoment W n m 1 q := by
  obtain ⟨E⟩ := C.charts (P.sourcePsi q) hq.2
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 (m:ℤ)
    (P.centers (m:ℤ)) (P.radii (m:ℤ)) (P.radii_pos _) (P.discs_eq _)
  rw [← P.normalized_cubic_primitive_contour C n m q hq]
  congr 1
  apply circleIntegral.integral_congr (P.radii_pos (m:ℤ)).le
  intro z hz
  dsimp only
  rw [P.filledCubicFrequencyIntegrand_eq_actual n q hq.1 z (D.sphere_subset_rootDomain hz),
    sourceFullAbelianPrimitive_index_shift E (m:ℤ) z
      (sourceCanonicalRootDomain_subset_openGapComplement (by simp) (by norm_num) _ (D.sphere_subset_rootDomain hz))]
  ring

theorem exists_finiteGap_cubic_contour_moment_formula (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) (hr : IsRealPeriodOneHminusOne q)
    (hf : {k : ℤ | canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (P.sourcePsi q))
      (periodOnePotential_mem _) k ≠ 0}.Finite) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sphere (0:ℂ) R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (P.sourcePsi q) →
      ∀ n : ℕ+, canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (P.sourcePsi q))
        (periodOnePotential_mem _) (n:ℤ) ≠ 0 →
      (2/(I*(Real.pi:ℂ))) *
        (∮ z in C(0,R), (sourceFullAbelianPrimitive (by simp) (by norm_num) W 0 (z,P.sourcePsi q))^3*
          P.abelianFrequencyDifferential n (z,q)) =
        (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries W n q := by
  let B := P.parent.parent.miuraBall.actionBall
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q (P.parent.subset (P.subset hq.1)).1 hr⟩
  let φ : realTypeSourceLocus 2 := hillMiuraRealSource u
  let D (k : ℤ) := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 k
    (P.centers k) (P.radii k) (P.radii_pos _) (P.discs_eq _)
  have hfamily : sourcePsiRealCenteredContourFamily (by simp) (by norm_num) φ.val
      (fun k => (P.centers k:ℂ)) P.radii :=
    ⟨fun _ => ofReal_im _,fun k => ⟨P.radii_pos k,(D k).gap,
      (D k).closedBall_subset_omittedDomain,(D k).sphere_subset_rootDomain⟩⟩
  obtain ⟨T,hT,hdec⟩ := exists_sourceFiniteGap_contour_decomposition (by simp) (by norm_num) φ hf
    (fun k => (P.centers k:ℂ)) P.radii hfamily
  refine ⟨T,hT,?_⟩
  intro R hR hcircle n hn
  let f : ℤ → ℂ := fun k => ∮ z in C((P.centers k:ℂ),P.radii k), P.filledCubicFrequencyIntegrand W n (z,q)
  have hzero (k : ℤ) (hk : k ∉ hf.toFinset) : f k=0 := by
    apply P.filledCubic_circle_eq_zero_of_gap_zero C n k q hq hr hn
    exact not_not.mp (fun hne => hk ((Set.Finite.mem_toFinset hf).mpr hne))
  have hs : Summable f := summable_of_ne_finset_zero hzero
  have heven : f.Even := fun k => P.filledCubic_opposite_circle_eq C n k q hq hr hn
  have hpair := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs
  have hf0 : f 0=0 := P.filledCubic_central_circle_eq_zero C n q hq
  simp only [hf0,zero_add,two_smul] at hpair
  have houter : (∮ z in C(0,R),
      (sourceFullAbelianPrimitive (by simp) (by norm_num) W 0 (z,P.sourcePsi q))^3*
        P.abelianFrequencyDifferential n (z,q)) = 2*∑' m : ℕ+, f (m:ℤ) := by
    calc
      _ = ∮ z in C(0,R), P.filledCubicFrequencyIntegrand W n (z,q) := by
        apply circleIntegral.integral_congr (hT.trans_le hR).le
        intro z hz
        exact (P.filledCubicFrequencyIntegrand_eq_actual n q hq.1 z (hcircle hz)).symm
      _ = ∑ k ∈ hf.toFinset, f k := hdec R hR _ (P.analytic_filledCubicFrequencyIntegrand C n q hq hr hn)
      _ = ∑' k : ℤ, f k := (tsum_eq_sum hzero).symm
      _ = _ := by simpa only [two_mul] using hpair
  have hpos : Summable (fun m : ℕ+ => f (m:ℤ)) := hs.comp_injective
    (fun a b hab => PNat.coe_injective (Int.ofNat_inj.mp hab))
  let v : ℕ+ → ℂ := fun m => (m:ℤ)*P.centeredMoment W n m 1 q
  let d : ℕ+ → ℂ := fun m => (2*(Real.pi:ℂ)*(n:ℤ))^3*(if m=n then 1 else 0)
  have hd : Summable d := summable_of_ne_finset_zero (s := {n}) (by
    intro m hm
    have hmn : m ≠ n := by simpa only [Finset.mem_singleton] using hm
    simp only [d,if_neg hmn,mul_zero])
  have hred (m : ℕ+) : (4/(I*(Real.pi:ℂ)))*f (m:ℤ)=d m-12*v m := by
    simpa only [f,d,v,mul_assoc] using P.filledCubic_positive_circle_reduction C n m q hq
  have hvs : Summable v := by
    have hscaled : Summable (fun m => 12*v m) := (hd.sub (hpos.mul_left (4/(I*(Real.pi:ℂ))))).congr
      (fun m => by linear_combination -hred m)
    have hv := hscaled.mul_left ((12:ℂ)⁻¹)
    simpa only [← mul_assoc,inv_mul_cancel₀ (by norm_num : (12:ℂ)≠0),one_mul] using hv
  have hsum : (∑' m : ℕ+, (4/(I*(Real.pi:ℂ)))*f (m:ℤ))=
      (∑' m : ℕ+, (d m - 12*v m)) := tsum_congr hred
  rw [tsum_mul_left,hd.tsum_sub (hvs.mul_left 12)] at hsum
  have hdval : (∑' m : ℕ+, d m)=(2*(Real.pi:ℂ)*(n:ℤ))^3 := by
    simp [d]
  rw [hdval] at hsum
  rw [tsum_mul_left] at hsum
  rw [houter]
  change _=(2*(Real.pi:ℂ)*(n:ℤ))^3-12*∑' m : ℕ+, v m
  rw [← hsum]
  ring

end NLS.KdV.HillProductEquationPatch
