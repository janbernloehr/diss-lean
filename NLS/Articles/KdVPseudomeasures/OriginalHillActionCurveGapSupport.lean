import NLS.Articles.KdVPseudomeasures.OriginalHillH1ActionCurve
import NLS.KdV.HillOnIndexRealClosedGap

/-! One finite signed index set contains every actual open Dirac gap
along the genuine selected-action curve, on any unchanged Miura patch. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1ActionCurve_gap_zero_of_base_gap_zero (n m : ℕ+) (hmn : m ≠ n)
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hm : hillHminusCanonicalGapSquare m (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))=0)
    (t : ℝ) :
    hillHminusCanonicalGapSquare m
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ActionCurve n q t)))=0 := by
  apply (hillIntegerSobolevEquiv_positive_eq_zero_iff_gapSquare _ m).mp
  rw [hillH1ActionCurve_native_image]
  have hmZ : (m:ℤ)≠(n:ℤ) := by intro h; exact hmn (PNat.coe_injective (Int.ofNat_inj.mp h))
  have hmpos : (0:ℤ)<(m:ℤ) := by exact_mod_cast m.pos
  have hnpos : (0:ℤ)<(n:ℤ) := by exact_mod_cast n.pos
  have hbase := (hillIntegerSobolevEquiv_positive_eq_zero_iff_gapSquare q m).mpr hm
  change _+(t:ℂ)*(hillH1ActionDirection n ((hillIntegerSobolevEquiv 1).equiv q)).val.val.val (m:ℤ)=0
  rw [hillH1ActionDirection,hillH1ModeCLM_apply,if_neg hmZ,if_neg (by omega : (m:ℤ)≠-(n:ℤ)),
    zero_add,mul_zero,add_zero,hbase]

theorem exists_hillH1ActionCurve_signed_gap_support (P : HillProductEquationPatch) (n : ℕ+)
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus) :
    ∃ S : Finset ℤ, ∀ t : ℝ,
      hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ActionCurve n q t)) ∈ P.source →
      ∀ k ∉ S, canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (P.sourcePsi
          (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ActionCurve n q t)))))
        (periodOnePotential_mem _) k=0 := by
  obtain ⟨N,hN⟩ := hf
  let B := max N (n:ℕ)
  refine ⟨Finset.Icc (-(B:ℤ)) (B:ℤ),fun t ht k hk => ?_⟩
  have hlarge : B < k.natAbs := by
    simp only [Finset.mem_Icc,not_and_or,not_le] at hk
    rcases hk with hk | hk <;> omega
  let m : ℕ+ := ⟨k.natAbs,by omega⟩
  have hmn : m ≠ n := by
    intro he
    have hb := le_max_right N (n:ℕ)
    change (n:ℕ) ≤ B at hb
    have hm : k.natAbs=(n:ℕ) := congrArg (fun j : ℕ+ => (j:ℕ)) he
    omega
  have hbase := hN m ((le_max_left N (n:ℕ)).trans hlarge.le)
  have hgap := hillH1ActionCurve_gap_zero_of_base_gap_zero n m hmn q hbase t
  let Q := hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ActionCurve n q t))
  have hr : IsRealPeriodOneHminusOne Q := (hillIntegerSourceInclusion 1 (hillH1ActionCurve n q t)).property
  have hpos := P.frequency_gap_zero_of_real_original_gap_zero m Q ht hr hgap
  by_cases hkpos : 0 ≤ k
  · have he : (m:ℤ)=k := by change (k.natAbs:ℤ)=k; omega
    rw [← he]
    exact hpos
  · have he : -(m:ℤ)=k := by change -(k.natAbs:ℤ)=k; omega
    have href : SourcePeriodicReflection (by simp) (by norm_num) (P.sourcePsi Q) :=
      sourcePeriodicReflection_hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift Q)
    rw [← he,href.gap_neg]
    exact hpos

end NLS.Articles.KdVPseudomeasures
