import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianCanonical
import NLS.Articles.KdVKdV2Frequencies.ArbitraryBaseAbelianRegularity

/-! # Global nonlinear Sobolev regularity of the SAME actual rough map

Both directions hold at arbitrary real rough sources, including sources
which are not initially L2. No local inverse or stronger source is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

theorem sobolev_iff_positive_mem (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (s : ℝ) (hs : -1 ≤ s) :
    Memℓp (fun j => (Weight.sobolev s j : ℂ)*q.val j) 2 ↔
      Memℓp (fun j => (Weight.sobolev (s+1) j : ℂ)*D.positive q j) 2 := by
  let q0 : PeriodOneRealHminusOne := ⟨q,hr⟩
  have hq : q ∈ ball q0.val (D.chart q0).data.radius := mem_ball_self (D.chart q0).data.radius_pos
  have H := (D.chart q0).sobolev_iff_weighted_positive_mem q hq hr s hs
  have he := D.positive_local q0 hq
  rw [←he] at H
  exact H

theorem signed_positive_real (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (j : ℤ) (hj : 0 < j) :
    (D.signed q).val j = D.positive q j/(Weight.sobolev (-1/2) j : ℂ) := by
  rw [signed,WeightedCoeff.signedTargetLift_apply,
    WeightedCoeff.normalizedSignedCompletion_apply _ (Weight.sobolev_neg (-1))]
  change (D.positive q j+conj (D.positive (periodOneHminusConjugation q) (-j)))/_ = _
  rw [(periodOneHminusConjugation_fixed_iff q).mpr hr,
    D.positive_zero q (D.real_mem_domain q hr) (-j) (by omega),map_zero,add_zero]

/-- Exact ALL-order nonlinear Sobolev criterion at EVERY real rough
source. In particular the inverse regularity direction does not assume
that the source already lies in the stronger Sobolev space. -/
theorem sobolev_iff_signed_mem (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (s : ℝ) (hs : -1 ≤ s) :
    Memℓp (fun j => (Weight.sobolev s j : ℂ)*q.val j) 2 ↔
      Memℓp (fun j => (Weight.sobolev (s+1/2) j : ℂ)*(D.signed q).val j) 2 := by
  have hsym (j : ℤ) : ‖(Weight.sobolev (s+1/2) (-j) : ℂ)*(D.signed q).val (-j)‖ =
      ‖(Weight.sobolev (s+1/2) j : ℂ)*(D.signed q).val j‖ := by
    rw [Weight.sobolev_neg,D.signed_real q hr j,norm_mul,norm_mul,norm_conj]
  have H := memlp_iff_positive_half_of_norm_neg_eq
    (p := 2) (fun j => (Weight.sobolev (s+1/2) j : ℂ)*(D.signed q).val j) hsym
  have he : (fun j : ℤ => if 0 < j then
      (Weight.sobolev (s+1/2) j : ℂ)*(D.signed q).val j else 0) =
      (fun j => (Weight.sobolev (s+1) j : ℂ)*D.positive q j) := by
    funext j
    by_cases hj : 0 < j
    · rw [if_pos hj,D.signed_positive_real q hr j hj]
      have hw : (Weight.sobolev (s+1/2) j : ℂ) =
          (Weight.sobolev (s+1) j : ℂ)*(Weight.sobolev (-1/2) j : ℂ) := by
        rw [show s+1/2 = (s+1)+(-1/2) by ring,Weight.sobolev_add,ofReal_mul]
      rw [hw,mul_assoc]
      exact congrArg (fun z : ℂ => (Weight.sobolev (s+1) j : ℂ)*z)
        (mul_div_cancel₀ (D.positive q j) (Weight.complex_ne_zero _ _))
    · rw [if_neg hj,D.positive_zero q (D.real_mem_domain q hr) j (by omega),mul_zero]
  rw [he] at H
  exact (D.sobolev_iff_positive_mem q hr s hs).trans H.symm

/-- A regular target at an arbitrary real rough source recovers an
ACTUAL original physical L2 source, not just an abstract membership witness. -/
theorem exists_physical_of_signed_half_mem (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hZ : Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*(D.signed q).val j) 2) :
    ∃ p : RealPeriodOneHillPotential, (hillPhysicalHminusEmbedding p).val = q := by
  have hq := (D.sobolev_iff_signed_mem q hr 0 (by norm_num)).mpr (by simpa only [zero_add] using hZ)
  have hm : Memℓp q.val 2 := by
    simpa only [Weight.sobolev_zero_apply,ofReal_one,one_mul] using hq
  let u : PeriodOneRealL2 := ⟨⟨q.val,hm⟩,hr⟩
  refine ⟨hillPhysicalRealL2Lift u,?_⟩
  rw [hillPhysicalRealL2Lift_hminus]
  apply Subtype.ext
  funext j
  exact periodOneL2Inclusion_apply u.val j

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
