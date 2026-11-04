import NLS.KdV.HillHminusOneIntrinsicDirichletColumn
import NLS.KdV.HillHminusOneDirichletGapLabels

/-! # Intrinsic original H^-1 Dirichlet endpoint norming factors

The terminal quasi-derivative at the nth actual Dirichlet gap label is
independent of every Miura lift and energy shift. It is real with the
exact sign (-1)^n, is a multiplier of the actual discriminant and has a
local complex analytic H^-1 extension. At a collapsed gap it equals
(-1)^n exactly. No common sequence-valued analytic domain is asserted.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory hiding extend
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

def hillHminusDirichletNorming (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) : ℂ :=
  extend ((hillHminusMiuraChartAt q).physicalMomentum q (hillHminusDirichletEnergy q hr n) (0,1)) 1

theorem hillHminusDirichletNorming_eq_chart (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusDirichletNorming q hr n =
      extend (C.physicalMomentum q (hillHminusDirichletEnergy q hr n) (0,1)) 1 := by
  let D := hillHminusMiuraChartAt q
  have hD : q ∈ D.domain := mem_hillHminusMiuraChartAt q
  exact D.dirichlet_momentum_eq_on_overlap_at_zero C q hD hq _
    ((D.hillHminusDirichlet_eq_physicalPosition q hD _).symm.trans (hillHminusDirichletEnergy_zero q hr n))

theorem hillHminusDirichletNorming_real (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (hillHminusDirichletNorming q hr n).im = 0 := by
  have h := (hillHminusMiuraChartAt q).physicalMomentum_dirichlet_terminal_star_real q
    (mem_hillHminusMiuraChartAt q) hr (hillHminusDirichletEnergy q hr n) (hillHminusDirichletEnergy_zero q hr n)
  have hi := congrArg Complex.im h
  change -(hillHminusDirichletNorming q hr n).im = (hillHminusDirichletNorming q hr n).im at hi
  linarith

theorem hillHminusDirichletNorming_characteristic (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (hillHminusDirichletNorming q hr n)^2-
      hillHminusDiscriminant q (hillHminusDirichletEnergy q hr n)*hillHminusDirichletNorming q hr n+1 = 0 :=
  (hillHminusMiuraChartAt q).dirichlet_terminal_multiplier q (mem_hillHminusMiuraChartAt q) _
    (hillHminusDirichletEnergy_zero q hr n)

theorem hillHminusDirichletNorming_signed_pos (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    0 < (-1 : ℝ)^(n : ℕ)*(hillHminusDirichletNorming q hr n).re := by
  let w := hillHminusDirichletNorming q hr n
  let D := (hillHminusDiscriminant q (hillHminusDirichletEnergy q hr n)).re
  let s : ℝ := (-1)^(n : ℕ)
  have hs : s^2 = 1 := by dsimp [s]; rw [← pow_mul,Nat.mul_comm (n : ℕ) 2,pow_mul]; norm_num
  have hw : w.im = 0 := hillHminusDirichletNorming_real q hr n
  have h := congrArg Complex.re (hillHminusDirichletNorming_characteristic q hr n)
  change (w^2-hillHminusDiscriminant q (hillHminusDirichletEnergy q hr n)*w+1).re = 0 at h
  have hquad : w.re^2-D*w.re+1 = 0 := by
    simpa only [pow_two,mul_re,sub_re,add_re,hw,mul_zero,zero_mul,sub_zero,one_re,zero_re,D] using h
  have hbound : 2 ≤ s*D := hillHminusDiscriminant_signed_gap_ge_two q hr (n : ℕ) n.property _
    (hillHminusDirichletEnergy_mem_gap q hr n)
  have hid : (s*D)*(s*w.re) = w.re^2+1 := by
    calc
      _ = s^2*(D*w.re) := by ring
      _ = w.re^2+1 := by rw [hs,one_mul]; linarith [hquad]
  have hp : 0 < (s*D)*(s*w.re) := by rw [hid]; positivity
  exact pos_of_mul_pos_right hp (by linarith)

theorem hillHminusDirichletNorming_ne_zero (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) : hillHminusDirichletNorming q hr n ≠ 0 := by
  intro h
  have hp := hillHminusDirichletNorming_signed_pos q hr n
  rw [h,zero_re,mul_zero] at hp
  exact lt_irrefl _ hp

theorem hillHminusDirichletNorming_eq_sign_of_closed_gap
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+)
    (hclosed : hillHminusRealLabels q hr (2*(n : ℕ)-1) = hillHminusRealLabels q hr (2*(n : ℕ))) :
    hillHminusDirichletNorming q hr n = (-1 : ℂ)^(n : ℕ) := by
  have hD : hillHminusDiscriminant q (hillHminusDirichletEnergy q hr n) = 2*(-1 : ℂ)^(n : ℕ) := by
    rw [hillHminusDirichletEnergy_eq_of_closed_gap q hr n hclosed]
    exact (hillHminusRealLabels_pair_trace q hr (n : ℕ) n.property).2
  have h := hillHminusDirichletNorming_characteristic q hr n
  rw [hD] at h
  have hs : ((-1 : ℂ)^(n : ℕ))^2 = 1 := by
    rw [← pow_mul,Nat.mul_comm (n : ℕ) 2,pow_mul]
    norm_num
  have he : (hillHminusDirichletNorming q hr n-(-1 : ℂ)^(n : ℕ))^2 = 0 := by linear_combination h+hs
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp he)

theorem hillHminusDirichletNorming_zero_potential (hr : IsRealPeriodOneHminusOne 0) (n : ℕ+) :
    hillHminusDirichletNorming 0 hr n = (-1 : ℂ)^(n : ℕ) := by
  apply hillHminusDirichletNorming_eq_sign_of_closed_gap
  simp only [hillHminusRealLabels_zero]
  have hl : (2*(n : ℕ)-1+1)/2 = (n : ℕ) := by have hp := n.property; omega
  have hu : (2*(n : ℕ)+1)/2 = (n : ℕ) := by omega
  rw [hl,hu]

theorem exists_hillHminusDirichletNorming_analytic_extension (q : PeriodOneRealHminusOne) (n : ℕ+) :
    ∃ b : PeriodOneHminusOne → ℂ, AnalyticAt ℂ b q.val ∧ b q.val = hillHminusDirichletNorming q.val q.property n ∧
      ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q, b p.val = hillHminusDirichletNorming p.val p.property n := by
  obtain ⟨a,ha,ha0,_,hmatch⟩ := exists_hillHminusDirichletEnergy_analytic_extension q n
  let C := hillHminusMiuraChartAt q.val
  have hq : q.val ∈ C.domain := mem_hillHminusMiuraChartAt q.val
  let b : PeriodOneHminusOne → ℂ := fun p => extend (C.physicalMomentum p (a p) (0,1)) 1
  have hm := (C.analyticOnNhd_physicalMomentum (0,1) (a q.val,q.val) ⟨mem_univ _,hq⟩).comp
    (f := fun p : PeriodOneHminusOne => (a p,p)) (ha.prod analyticAt_id)
  have hb : AnalyticAt ℂ b q.val := by
    have he := ((ContinuousMap.evalCLM ℂ (⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)).analyticAt _).comp hm
    apply he.congr
    exact Filter.Eventually.of_forall (fun p =>
      (extend_coe (C.physicalMomentum p (a p) (0,1)) ⟨1,by constructor <;> norm_num⟩).symm)
  refine ⟨b,hb,?_,?_⟩
  · change extend (C.physicalMomentum q.val (a q.val) (0,1)) 1 = _
    rw [ha0,← hillHminusDirichletNorming_eq_chart C q.val hq q.property n]
  have hdom : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q, p.val ∈ C.domain :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (C.domain_open.mem_nhds hq)
  filter_upwards [hmatch,hdom] with p hp hd
  change extend (C.physicalMomentum p.val (a p.val) (0,1)) 1 = _
  rw [hp,← hillHminusDirichletNorming_eq_chart C p.val hd p.property n]

theorem continuous_hillHminusDirichletNorming (n : ℕ+) :
    Continuous (fun q : PeriodOneRealHminusOne => hillHminusDirichletNorming q.val q.property n) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨b,hb,_,he⟩ := exists_hillHminusDirichletNorming_analytic_extension q n
  have heq : (fun p : PeriodOneRealHminusOne => hillHminusDirichletNorming p.val p.property n) =ᶠ[𝓝 q]
      (fun p : PeriodOneRealHminusOne => b p.val) := he.mono (fun _ hp => hp.symm)
  exact (hb.continuousAt.comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq heq

end NLS.KdV
