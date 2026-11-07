import NLS.KdV.HillRoughSignedDerivativeInjective

/-! # Actual signed coordinate differentials determine a rough mean-zero direction -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem signed_fderiv_component (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hq : q∈D.domain) (h : PeriodOneHminusOne) (σ : Bool) (n : ℕ+) :
    (fderiv ℂ (hillRoughSignedAbelianComponent D.signed σ n) q) h=
      (fderiv ℂ D.signed q h).val (if σ then (n : ℤ) else -(n : ℤ)) := by
  have hd := ((WeightedCoeff.evalCLM (Weight.sobolev (-1/2)) 2
    (if σ then (n : ℤ) else -(n : ℤ))).hasFDerivAt.comp q
      (D.signed_analytic q hq).differentiableAt.hasFDerivAt).fderiv
  change fderiv ℂ (hillRoughSignedAbelianComponent D.signed σ n) q=_ at hd
  rw [hd]
  rfl

theorem signed_fderiv_zero_mode (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hq : q∈D.domain) (h : PeriodOneHminusOne) :
    (fderiv ℂ D.signed q h).val 0=0 := by
  let E := WeightedCoeff.evalCLM (Weight.sobolev (-1/2)) 2 0
  have hd := (E.hasFDerivAt.comp q (D.signed_analytic q hq).differentiableAt.hasFDerivAt).fderiv
  have he : (fun p : PeriodOneHminusOne => E (D.signed p))=ᶠ[𝓝 q] fun _ => (0 : ℂ) := by
    filter_upwards [D.domain_open.mem_nhds hq] with p hp
    exact D.signed_zero p hp
  have hzero : fderiv ℂ (fun p : PeriodOneHminusOne => E (D.signed p)) q=0 := by
    rw [he.fderiv_eq,fderiv_const_apply]
  have ht := congrArg (fun T : PeriodOneHminusOne →L[ℂ] ℂ => T h) (hd.symm.trans hzero)
  exact ht

theorem meanZero_direction_eq_of_signed_components (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0=0)
    (v w : PeriodOneHminusOne) (hv : v.val 0=0) (hw : w.val 0=0)
    (he : ∀ σ : Bool, ∀ n : ℕ+,
      (fderiv ℂ (hillRoughSignedAbelianComponent D.signed σ n) q) v=
        (fderiv ℂ (hillRoughSignedAbelianComponent D.signed σ n) q) w) : v=w := by
  have hq := D.real_mem_domain q hr
  apply D.signed_fderiv_injective_on_meanZero q hr hm v w hv hw
  apply Subtype.ext
  funext j
  rcases lt_trichotomy 0 j with hj|hj|hj
  · let n : ℕ+ := ⟨j.toNat,by omega⟩
    have hn : (n : ℤ)=j := Int.toNat_of_nonneg hj.le
    have h := he true n
    rw [D.signed_fderiv_component q hq,D.signed_fderiv_component q hq] at h
    simpa only [ite_true,hn] using h
  · subst j
    rw [D.signed_fderiv_zero_mode q hq,D.signed_fderiv_zero_mode q hq]
  · let n : ℕ+ := ⟨(-j).toNat,by omega⟩
    have hn : (n : ℤ)= -j := Int.toNat_of_nonneg (by omega)
    have h := he false n
    rw [D.signed_fderiv_component q hq,D.signed_fderiv_component q hq] at h
    simpa only [Bool.false_eq_true,ite_false,hn,neg_neg] using h

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
