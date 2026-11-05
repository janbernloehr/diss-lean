import NLS.KdV.HillHminusOnePairUniqueness
import NLS.KdV.HillRealSpectrum
import NLS.SequenceSpaces.PeriodOneHminusOneRealDensity
import NLS.ComplexAnalysis.ClosedZeroPersistence

/-! # Reality of the actual full H^-1 Hill characteristic

Real finite Fourier truncations approximate every real H^-1 potential.
Joint continuity of the entire trace and local analytic zero-count
stability extend the physical L2 reality theorem to all characteristic
zeros, including central and multiple zeros. Nontriviality follows from
the already constructed high two-root count.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ComplexConjugate Classical
namespace NLS.KdV

/-- Unit-period Fourier reality is retained by the explicit period doubling. -/
theorem IsRealHillPotential.periodDouble {a : Coeff 2} (ha : IsRealHillPotential a) :
    IsRealHillPotential (Coeff.periodDouble a) := by
  intro k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he,show -(2*(k/2)) = 2*(-(k/2)) by ring,Coeff.periodDouble_even,
      Coeff.periodDouble_even,ha]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,show -(2*(k/2)+1) = 2*(-(k/2)-1)+1 by ring,
      Coeff.periodDouble_odd,Coeff.periodDouble_odd,map_zero]

/-- The existing physical L2 theorem in the original unit-period convention. -/
theorem hillL2_periodDouble_root_im_zero (a : Coeff 2) (ha : IsRealHillPotential a)
    (z : ℂ) (hz : hillL2Radicand (Coeff.periodDouble a) z = 0) : z.im = 0 := by
  let Q : WeightedCoeff SpectralWeight.one.toWeight 2 :=
    ⟨Coeff.periodDouble a,by
      change Memℓp (fun k => (SpectralWeight.one.toWeight k : ℂ)*Coeff.periodDouble a k) 2
      simpa using lp.memℓp (Coeff.periodDouble a)⟩
  have hQ : SpectralWeight.one.toCoeff Q = Coeff.periodDouble a := by ext k; exact SpectralWeight.toCoeff_apply _ _ k
  apply hillL2Discriminant_root_im_zero Q
    (by rw [hQ]; exact Coeff.periodDouble_mem a) (by rw [hQ]; exact ha.periodDouble)
  rw [hQ]
  exact sub_eq_zero.mp hz

/-- The actual H^-1 radicand is nonconstant for every complex potential.
Its already proved total count of two excludes every constant slice. -/
theorem hillHminusRadicand_not_constant (q : PeriodOneHminusOne) :
    ¬ ∃ c : ℂ, ∀ z : ℂ, hillHminusRadicand q z = c := by
  obtain ⟨r,N,V,_,_,hN,_,hq,hfamily⟩ := exists_hillHminus_high_gap_pairs q
  let n : ℕ+ := ⟨N,hN⟩
  obtain ⟨_,_,_,_,_,_,hpairs⟩ := hfamily n le_rfl
  obtain ⟨_,l,u,hpair,_⟩ := hpairs q hq
  have hcount := hpair.analyticZeroCount_eq_two
  rintro ⟨c,hc⟩
  have he : (fun z => hillHminusRadicand q z) = (fun _ : ℂ => c) := funext hc
  rw [he,analyticZeroCount_const] at hcount
  norm_num at hcount

theorem exists_hillHminusRadicand_ne_zero (q : PeriodOneHminusOne) :
    ∃ z : ℂ, hillHminusRadicand q z ≠ 0 := by
  by_contra h
  exact hillHminusRadicand_not_constant q ⟨0,fun z => not_ne_iff.mp (not_exists.mp h z)⟩

theorem hillHminusDiscriminant_not_constant (q : PeriodOneHminusOne) :
    ¬ ∃ c : ℂ, ∀ z : ℂ, hillHminusDiscriminant q z = c := by
  rintro ⟨c,hc⟩
  apply hillHminusRadicand_not_constant q
  refine ⟨c^2-4,?_⟩
  intro z
  simp only [hillHminusRadicand,hc z]

/-- Every energy order is finite, including all central and multiple zeros. -/
theorem analyticOrderAt_hillHminusRadicand_ne_top (q : PeriodOneHminusOne) (z : ℂ) :
    analyticOrderAt (fun w => hillHminusRadicand q w) z ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ (fun w => hillHminusRadicand q w) univ := by
    intro w _
    exact (analyticOnNhd_hillHminusRadicand_joint (w,q) (mem_univ _)).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  obtain ⟨b,hb⟩ := exists_hillHminusRadicand_ne_zero q
  exact analyticOrderAt_ne_top_on_connected isPreconnected_univ ha (mem_univ b) hb (mem_univ z)

/-- Every actual characteristic zero of a real unit-period H^-1 potential
is real. There is no high-energy, simplicity or mean-zero hypothesis. -/
theorem hillHminusRadicand_root_im_zero (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : hillHminusRadicand q z = 0) : z.im = 0 := by
  let F : PeriodOneRealHminusOne → ℂ → ℂ := fun a z => hillHminusRadicand a.val z
  have hF : Continuous F.uncurry := by
    change Continuous (fun p : PeriodOneRealHminusOne × ℂ => hillHminusRadicand p.1.val p.2)
    have hD : Continuous (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1) :=
      analyticOnNhd_hillHminusRadicand_joint.continuous
    have hm : Continuous (fun p : PeriodOneRealHminusOne × ℂ => (p.2,p.1.val)) :=
      continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
    exact Continuous.comp (g := fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1)
      (f := fun p : PeriodOneRealHminusOne × ℂ => (p.2,p.1.val)) hD hm
  have ha (a : PeriodOneRealHminusOne) : AnalyticOnNhd ℂ (F a) univ := by
    intro z _
    exact (analyticOnNhd_hillHminusRadicand_joint (z,a.val) (mem_univ _)).comp
      (f := fun z : ℂ => (z,a.val)) (analyticAt_id.prod analyticAt_const)
  obtain ⟨b,hb⟩ := exists_hillHminusRadicand_ne_zero q
  apply zero_mem_closed_of_closure_parameters F hF ha (range periodOneRealL2Inclusion)
    {z : ℂ | z.im = 0} (isClosed_eq continuous_im continuous_const) ?_
    ⟨q,hq⟩ (denseRange_periodOneRealL2Inclusion ⟨q,hq⟩) b hb z hz
  rintro a ⟨v,rfl⟩ w hw
  have he : hillL2Radicand (Coeff.periodDouble v.val) w = 0 := by
    simpa only [F,periodOneRealL2Inclusion,hillHminusRadicand_eq_hillL2] using hw
  exact hillL2_periodDouble_root_im_zero v.val v.property w he

/-- Equivalent trace formulation at either periodic or antiperiodic level. -/
theorem hillHminusDiscriminant_root_im_zero (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : hillHminusDiscriminant q z^2 = 4) :
    z.im = 0 := hillHminusRadicand_root_im_zero q hq z (sub_eq_zero.mpr hz)

/-- Both entries of every constructed high pair are real, including a double root. -/
theorem HillHminusHighGapPair.im_eq_zero {q : PeriodOneHminusOne}
    (hq : IsRealPeriodOneHminusOne q) {n : ℕ+} {r : ℝ} {l u : ℂ}
    (h : HillHminusHighGapPair q n r l u) : l.im = 0 ∧ u.im = 0 :=
  ⟨hillHminusRadicand_root_im_zero q hq l h.left_zero,
    hillHminusRadicand_root_im_zero q hq u h.right_zero⟩

/-- The actual source sheets cover both full nonreal half-planes at every
real H^-1 potential, not just the high contours. -/
theorem mem_hillHminusContinuationDomain_of_im_ne_zero
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z.im ≠ 0) : (z,q) ∈ hillHminusContinuationDomain := by
  rw [mem_hillHminusContinuationDomain_iff]
  refine ⟨mem_slitPlane_iff.mpr (Or.inr hz),?_⟩
  intro s _ hs
  exact hz (hillHminusRadicand_root_im_zero _ (hq.smul_real s) z hs)

theorem analyticOnNhd_hillHminusContinuedRoot_off_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    AnalyticOnNhd ℂ (fun z => hillHminusContinuedRoot (z,q)) {z : ℂ | z.im ≠ 0} := by
  intro z hz
  exact (analyticOnNhd_hillHminusContinuedRoot _
    (mem_hillHminusContinuationDomain_of_im_ne_zero q hq z hz)).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

theorem analyticOnNhd_hillHminusContinuedPrimitive_off_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    AnalyticOnNhd ℂ (fun z => hillHminusContinuedPrimitive (z,q)) {z : ℂ | z.im ≠ 0} := by
  intro z hz
  exact (analyticOnNhd_hillHminusContinuedPrimitive _
    (mem_hillHminusContinuationDomain_of_im_ne_zero q hq z hz)).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

end NLS.KdV
