import NLS.KdV.HillHminusOneDirichletLowerExterior
import NLS.KdV.HillHminusOneDirichletGapLabels
import NLS.KdV.HillHminusOneLabelCofinality

/-! # The positive-gap labels exhaust the actual intrinsic Dirichlet spectrum

Reality, lower-exterior exclusion, canonical endpoint cofinality and
open-band exclusion place every actual zero in one positive gap. Its
proved uniqueness identifies that zero with the intrinsic gap label.
Every weak Dirichlet energy is therefore exactly one of these labels.
All characteristic zeros at real potentials have analytic order one.
Closed operator domains and periodic multiplicities are not inferred.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.LinearVolterra
namespace NLS.KdV

theorem hillHminusDirichlet_real_zero_eq_label (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (x : ℝ) (hz : hillHminusDirichlet q x = 0) :
    ∃ n : ℕ+, x = hillHminusDirichletEnergy q hr n := by
  have hlow : hillHminusRealLabels q hr 0 < x := by
    by_contra! h
    exact hillHminusDirichlet_ne_zero_at_or_below_lowest q hr x h hz
  have hex := exists_hillHminusRealLabels_gap_upper_ge q hr x
  let m := Nat.find hex
  have hm : x ≤ hillHminusRealLabels q hr (2*(m+1)) := Nat.find_spec hex
  have hprev : hillHminusRealLabels q hr (2*m) < x := by
    by_cases hm0 : m = 0
    · simpa only [hm0,mul_zero] using hlow
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hnot := Nat.find_min hex (show m-1 < Nat.find hex from Nat.sub_lt hmpos (by norm_num))
    have hi : m-1+1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hmpos)
    change ¬ x ≤ hillHminusRealLabels q hr (2*(m-1+1)) at hnot
    rw [hi] at hnot
    exact lt_of_not_ge hnot
  have hgap : hillHminusRealLabels q hr (2*m+1) ≤ x := by
    by_contra! h
    exact hillHminusDirichlet_ne_zero_on_open_band q hr m x ⟨hprev,h⟩ hz
  let n : ℕ+ := ⟨m+1,Nat.succ_pos m⟩
  refine ⟨n,?_⟩
  apply (hillHminusDirichletEnergy_eq_of_zero_in_gap q hr n x ?_ hz).symm
  change x ∈ Icc (hillHminusRealLabels q hr (2*(m+1)-1)) (hillHminusRealLabels q hr (2*(m+1)))
  rw [show 2*(m+1)-1 = 2*m+1 by omega]
  exact ⟨hgap,hm⟩

theorem hillHminusDirichlet_zero_iff_label (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ) :
    hillHminusDirichlet q lambda = 0 ↔ ∃ n : ℕ+, lambda = (hillHminusDirichletEnergy q hr n : ℂ) := by
  constructor
  · intro hz
    have him := hillHminusDirichlet_zero_energy_im_zero q hr lambda hz
    have he : (lambda.re : ℂ) = lambda := by apply Complex.ext <;> simp [him]
    have hzr : hillHminusDirichlet q lambda.re = 0 := by rw [he]; exact hz
    obtain ⟨n,hn⟩ := hillHminusDirichlet_real_zero_eq_label q hr lambda.re hzr
    exact ⟨n,he.symm.trans (congrArg Complex.ofReal hn)⟩
  · rintro ⟨n,rfl⟩
    exact hillHminusDirichletEnergy_zero q hr n

theorem intrinsic_dirichlet_energy_iff_label (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ) :
    (∃ y : Curve ℂ, IsIntrinsicHillDirichletEigenfunction q lambda y) ↔
      ∃ n : ℕ+, lambda = (hillHminusDirichletEnergy q hr n : ℂ) :=
  (hillHminusDirichlet_eq_zero_iff_intrinsic_dirichlet q lambda).symm.trans
    (hillHminusDirichlet_zero_iff_label q hr lambda)

theorem hillHminusDirichlet_zero_has_unique_label (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ) (hz : hillHminusDirichlet q lambda = 0) :
    ∃! n : ℕ+, lambda = (hillHminusDirichletEnergy q hr n : ℂ) := by
  obtain ⟨n,hn⟩ := (hillHminusDirichlet_zero_iff_label q hr lambda).mp hz
  refine ⟨n,hn,?_⟩
  intro m hm
  exact (strictMono_hillHminusDirichletEnergy q hr).injective
    (Complex.ofReal_injective (hm.symm.trans hn))

end NLS.KdV
