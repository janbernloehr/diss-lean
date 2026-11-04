import NLS.KdV.HillHminusOneMiuraSpectralInvariance
import NLS.KdV.HillHminusOneOriginalContourRoots
import NLS.KdV.HillHminusOneUniformPrimitiveBounds

/-! # Spectral invariance of the actual rough Hill sheets near zero

A common free logarithmic strip, including the finite contour head, fixes
the primitive integer ambiguity. Actual canonical roots on a real-preserving
Miura chart fix the root sign. Thus equal intrinsic Hill discriminants give
the same continued root and primitive on every original positive contour,
on one rough-input ball chosen before both inputs and every index.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
namespace HillHminusAllContourPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne}
variable (D : HillHminusAllContourPeriodData C N V)
include D

/-- The high strip and finitely many compact free-circle tubes give a single imaginary strip for every original contour. -/
theorem exists_uniform_primitive_strip :
    ∃ U : Set PeriodOneHminusOne, U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, ∀ k : ℕ+, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
        |(hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi).im| < Real.pi/2 := by
  obtain ⟨M,Vs,_,hVs,h0Vs,hstrip⟩ := exists_hillHminus_high_primitive_strip 0
  have hfixed (k : ℕ+) : ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
        ‖hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi‖ ≤ 3*Real.pi/8 := by
    apply exists_compact_slice_norm_bound
      (fun t : ℂ × PeriodOneHminusOne => hillHminusContinuedPrimitive (t.1^2,t.2)+I*(k : ℂ)*Real.pi)
      ((fun t : ℂ × PeriodOneHminusOne => (t.1^2,t.2)) ⁻¹' hillHminusContinuationDomain)
      (isOpen_hillHminusContinuationDomain.preimage ((continuous_fst.pow 2).prodMk continuous_snd))
      (show ContinuousOn _ _ from (by
        intro t ht
        exact (((analyticOnNhd_hillHminusContinuedPrimitive (t.1^2,t.2) ht).comp
          (f := fun u : ℂ × PeriodOneHminusOne => (u.1^2,u.2))
          ((analyticAt_fst.pow 2).prod analyticAt_snd)).add analyticAt_const).continuousAt.continuousWithinAt))
      _ (isCompact_sphere _ _) 0 (3*Real.pi/8) (D.cover k 0 D.zero_mem)
    intro z hz
    have he : hillHminusContinuedPrimitive (z^2,0)+I*(k : ℂ)*Real.pi =
        -I*(z-(Real.pi : ℂ)*(k : ℕ)) := by
      rw [hillHminusContinuedPrimitive_base,
        show -I*Complex.sqrt (z^2) = -I*z from
          classicalHillFreePrimitive_sq_of_re_pos z
            (re_pos_of_high_closedBall _ k.property z (sphere_subset_closedBall hz))]
      ring
    rw [he,norm_mul,norm_neg,norm_I,one_mul,mem_sphere_iff_norm.mp hz]
    linarith [Real.pi_pos]
  let U (k : ℕ+) := (hfixed k).choose
  have hU (k : ℕ+) := (hfixed k).choose_spec
  let B : Fin (M+1) → Set PeriodOneHminusOne := fun i =>
    if hi : 0 < i.val then U ⟨i.val,hi⟩ else univ
  have hB (i : Fin (M+1)) : IsOpen (B i) ∧ (0 : PeriodOneHminusOne) ∈ B i := by
    by_cases hi : 0 < i.val
    · simpa only [B,dif_pos hi] using ⟨(hU ⟨i.val,hi⟩).1,(hU ⟨i.val,hi⟩).2.1⟩
    · simp only [B,dif_neg hi]
      exact ⟨isOpen_univ,mem_univ _⟩
  let W := (V ∩ Vs) ∩ ⋂ i, B i
  refine ⟨W,fun _ hq => hq.1.1,
    (D.isOpen.inter hVs).inter (isOpen_iInter_of_finite fun i => (hB i).1),
    ⟨⟨D.zero_mem,h0Vs⟩,mem_iInter.mpr (fun i => (hB i).2)⟩,?_⟩
  intro q hq k z hz
  by_cases hk : (k : ℕ) ≤ M
  · have hi := mem_iInter.mp hq.2 (⟨(k : ℕ),Nat.lt_succ_of_le hk⟩ : Fin (M+1))
    have hb := (hU k).2.2 q (by simpa only [B,dif_pos k.pos] using! hi) z hz
    exact (abs_im_le_norm _).trans_lt (hb.trans_lt (by linarith [Real.pi_pos]))
  · exact hstrip q hq.1.2 (k : ℕ) (Nat.lt_of_not_ge hk).le z
      (sphere_subset_closedBall hz) (D.cover k q hq.1.1 z hz)

end HillHminusAllContourPeriodData
/-- Literal equality of the root and primitive follows from equal real-input discriminants, with their signs and logarithmic phases fixed. -/
theorem exists_hillHminus_isospectral_continued_sheets (Dold : HillHminusMiuraChart)
    {N : ℕ} {U : Set PeriodOneHminusOne} (D : HillHminusAllContourPeriodData Dold N U) :
    ∃ δ : ℝ, 0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ U ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ p ∈ ball (0 : PeriodOneHminusOne) δ,
        periodOneHminusConjugation q = q → periodOneHminusConjugation p = p →
        hillHminusDiscriminant p = hillHminusDiscriminant q →
        ∀ k : ℕ+, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
          hillHminusContinuedRoot (z^2,p) = hillHminusContinuedRoot (z^2,q) ∧
          hillHminusContinuedPrimitive (z^2,p) = hillHminusContinuedPrimitive (z^2,q) := by
  obtain ⟨C,V,W₀,W,s,hV,h0,hVC,_,hpos,hc,hr,H,hW,_,_,_⟩ :=
    exists_hillHminus_real_normalized_energy_pullbacks 0 periodOneHminusConjugation_zero
  obtain ⟨Us,hUsU,hUs,h0Us,hstrip⟩ := D.exists_uniform_primitive_strip
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp (hV.inter hUs) 0 ⟨h0,h0Us⟩
  have hδU : ball (0 : PeriodOneHminusOne) δ ⊆ U := fun _ hq => hUsU (hball hq).2
  have hrV : ∀ q ∈ V, periodOneHminusConjugation q = q →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource q)) := fun q hq hqr => (hr q (hVC hq) hqr).2
  have hroot (q : PeriodOneHminusOne) (hq : q ∈ ball (0 : PeriodOneHminusOne) δ)
      (hqr : periodOneHminusConjugation q = q) (k : ℕ+)
      (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      C.energyRoot q (z^2) = hillHminusContinuedRoot (z^2,q) := by
    have hpath (r : ℝ) (hrange : r ∈ Icc (0 : ℝ) 1) : (r : ℂ) • q ∈ V := by
      apply (fun hx => (hball hx).1)
      rw [mem_ball_zero_iff,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrange.1]
      exact (mul_le_of_le_one_left (norm_nonneg q) hrange.2).trans_lt (mem_ball_zero_iff.mp hq)
    exact C.energyRoot_eq_continuedRoot_of_real_segment H hV hVC hW h0 hc hrV q hqr hpath
      ⟨hillHminus_original_contour_mem_energyRootDomain C Dold D q (hδU hq)
        (hVC (hball hq).1) hqr hpos hc (hrV q (hball hq).1 hqr) k z hz,
        D.cover k q (hδU hq) z hz⟩
  refine ⟨δ,hδ,hδU,?_⟩
  intro q hq p hp hqr hpr htrace k z hz
  have hR : hillHminusContinuedRoot (z^2,p) = hillHminusContinuedRoot (z^2,q) := by
    rw [← hroot p hp hpr k z hz,← hroot q hq hqr k z hz]
    exact hillHminusMiuraChart_energyRoot_eq_of_discriminant_eq C q p
      (hVC (hball hq).1) (hVC (hball hp).1)
      (hrV q (hball hq).1 hqr) (hrV p (hball hp).1 hpr) htrace _
  refine ⟨hR,?_⟩
  have hexp : exp (hillHminusContinuedPrimitive (z^2,p)) = exp (hillHminusContinuedPrimitive (z^2,q)) := by
    rw [show hillHminusContinuedPrimitive = hillHminusSourceFamily.primitive from rfl,
      hillHminusSourceFamily.exp_primitive _ (D.cover k p (hδU hp) z hz),
      hillHminusSourceFamily.exp_primitive _ (D.cover k q (hδU hq) z hz)]
    change (hillHminusDiscriminant p (z^2)+hillHminusContinuedRoot (z^2,p))/2 =
      (hillHminusDiscriminant q (z^2)+hillHminusContinuedRoot (z^2,q))/2
    rw [htrace,hR]
  apply eq_of_exp_eq_of_abs_im_sub_le_pi _ _ hexp
  have hsQ := abs_lt.mp (hstrip q (hball hq).2 k z hz)
  have hsP := abs_lt.mp (hstrip p (hball hp).2 k z hz)
  simp only [add_im] at hsQ hsP
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end NLS.KdV
