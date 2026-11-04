import NLS.KdV.HillFreeUniformInverseChart
import NLS.KdV.HillComplexPeriodAnalytic
import NLS.SequenceSpaces.PositiveDeletedContraction

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The actual complex free-contour period equations restricted to the
original positive deleted root-coordinate space. -/
def hillComplexFreeSupportedPeriodMap (n : ℕ)
    (t : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) : PositiveDeletedCoeff 2 (n : ℤ) :=
  Coeff.positiveDeletedProjectionTo 2 (n : ℤ)
    (hillComplexScaledPeriodSequence hq hr n ((t.1 : Coeff 2),t.2))

theorem analyticOnNhd_hillComplexFreeSupportedPeriodMap (n : ℕ) (hn : 1≤n)
    (ε D : ℝ) (hD : 0≤D) (hc : HillComplexPeriodControl hq hr ε D) :
    AnalyticOnNhd ℂ (hillComplexFreeSupportedPeriodMap hq hr n) (univ ×ˢ ball 0 ε) := by
  let inc := (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  intro t ht
  have hpair : AnalyticAt ℂ (fun v : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 => ((v.1 : Coeff 2),v.2)) t :=
    ((inc.analyticAt t.1).comp (f := fun v : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 => v.1) analyticAt_fst).prod
      analyticAt_snd
  have hseq := (analyticOnNhd_hillComplexScaledPeriodSequence hq hr n hn ε D hD hc
    ((t.1 : Coeff 2),t.2) ⟨mem_univ _,ht.2⟩).comp
      (f := fun v : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 => ((v.1 : Coeff 2),v.2)) hpair
  exact ((Coeff.positiveDeletedProjectionTo 2 (n : ℤ)).analyticAt _).comp hseq

/-- The original complex period map is a uniformly controlled perturbation
of the original free period map, in the same deleted Hilbert space. -/
theorem norm_hillComplexFreeSupportedPeriodMap_sub_free_le (n : ℕ) (hn : 1≤n)
    (ε D : ℝ) (hD : 0≤D) (hc : HillComplexPeriodControl hq hr ε D)
    (a : PositiveDeletedCoeff 2 (n : ℤ)) (p : Coeff 2) (hp : ‖p‖≤ε) :
    ‖hillComplexFreeSupportedPeriodMap hq hr n (a,p)-hillFreeSupportedPeriodMap hq hr n hn a‖ ≤
      2*D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖ := by
  change ‖(Coeff.positiveDeletedProjectionTo 2 (n : ℤ))
      (hillComplexScaledPeriodSequence hq hr n ((a : Coeff 2),p))-
    (Coeff.positiveDeletedProjectionTo 2 (n : ℤ))
      (hillFreeScaledPeriodSequence hq hr n hn (a : Coeff 2))‖≤_
  rw [← map_sub]
  apply (Coeff.norm_positiveDeletedProjectionTo_le 2 (n : ℤ) _).trans
  simpa only [Submodule.norm_coe] using norm_hillComplexScaledPeriodSequence_sub_free_le hq hr n hn
    (a : Coeff 2) p D hD (fun k hk hnk => (hc p hp).2 n k hn hk hnk (a : Coeff 2))

theorem hillComplexFreeSupportedPeriodMap_at_zero_parameter (n : ℕ) (hn : 1≤n)
    (ε D : ℝ) (hε : 0≤ε) (hD : 0≤D) (hc : HillComplexPeriodControl hq hr ε D)
    (a : PositiveDeletedCoeff 2 (n : ℤ)) :
    hillComplexFreeSupportedPeriodMap hq hr n (a,0)=hillFreeSupportedPeriodMap hq hr n hn a := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [norm_zero,mul_zero] using
    norm_hillComplexFreeSupportedPeriodMap_sub_free_le hq hr n hn ε D hD hc a 0 (by simpa using hε)

theorem norm_hillComplexFreeSupportedPeriodMap_le (n : ℕ) (hn : 1≤n)
    (ε D : ℝ) (hD : 0≤D) (hc : HillComplexPeriodControl hq hr ε D)
    (a : PositiveDeletedCoeff 2 (n : ℤ)) (p : Coeff 2) (hp : ‖p‖≤ε) :
    ‖hillComplexFreeSupportedPeriodMap hq hr n (a,p)‖≤
      Real.exp ((2/Real.pi^2)*‖a‖)*‖a‖+2*D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖ := by
  exact (norm_le_norm_sub_add (hillComplexFreeSupportedPeriodMap hq hr n (a,p))
    (hillFreeSupportedPeriodMap hq hr n hn a)).trans
      ((add_le_add (norm_hillComplexFreeSupportedPeriodMap_sub_free_le hq hr n hn ε D hD hc a p hp)
        (norm_hillFreeSupportedPeriodMap_le hq hr n hn a)).trans_eq (by ring))

/-- The root block of the actual joint complex period derivative at the
free source is exactly minus identity, without choosing a root family. -/
theorem hillComplexFreeSupportedPeriodMap_root_derivative_zero (n : ℕ) (hn : 1≤n)
    (ε D : ℝ) (hε : 0<ε) (hD : 0≤D) (hc : HillComplexPeriodControl hq hr ε D) :
    (fderiv ℂ (hillComplexFreeSupportedPeriodMap hq hr n) (0,0)).comp
      (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)) =
        -ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ)) := by
  have hF := analyticOnNhd_hillComplexFreeSupportedPeriodMap hq hr n hn ε D hD hc
    (0,0) ⟨mem_univ _,mem_ball_self hε⟩
  have hi : HasFDerivAt (fun a : PositiveDeletedCoeff 2 (n : ℤ) => (a,(0 : Coeff 2)))
      (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)) 0 :=
    hasFDerivAt_prodMk_left 0 0
  have hd := hF.differentiableAt.hasFDerivAt.comp (f := fun a : PositiveDeletedCoeff 2 (n : ℤ) => (a,(0 : Coeff 2))) 0 hi
  have he : (fun a : PositiveDeletedCoeff 2 (n : ℤ) => hillComplexFreeSupportedPeriodMap hq hr n (a,0))=
      hillFreeSupportedPeriodMap hq hr n hn :=
    funext (hillComplexFreeSupportedPeriodMap_at_zero_parameter hq hr n hn ε D hε.le hD hc)
  simp only [Function.comp_def] at hd
  rw [he] at hd
  exact hd.unique (hasFDerivAt_hillFreeSupportedPeriodMap_zero hq hr n hn)

/-- Exact coordinate recovery in the common complex period domain. -/
theorem hillComplexFreeSupportedPeriodMap_apply_on (n : ℕ) (hn : 1≤n)
    (ε D : ℝ) (hD : 0≤D) (hc : HillComplexPeriodControl hq hr ε D)
    (a : PositiveDeletedCoeff 2 (n : ℤ)) (p : Coeff 2) (hp : p∈ball 0 ε) (m : ℤ) :
    (hillComplexFreeSupportedPeriodMap hq hr n (a,p) : Coeff 2) m =
      hillComplexScaledPeriodCoordinate hq hr n ((a : Coeff 2),p) m := by
  change Coeff.positiveDeletedProjection 2 (n : ℤ)
    (hillComplexScaledPeriodSequence hq hr n ((a : Coeff 2),p)) m=_
  rw [Coeff.positiveDeletedProjection_apply]
  by_cases hm : 0<m ∧ m≠(n : ℤ)
  · rw [if_pos hm]
    exact hillComplexScaledPeriodSequence_apply_on hq hr n hn ε D hD hc
      ((a : Coeff 2),p) ⟨mem_univ _,hp⟩ m
  · rw [if_neg hm,hillComplexScaledPeriodCoordinate,if_neg hm]

/-- A zero in the actual deleted space is precisely the original system
of all off-diagonal complex Abelian periods. -/
theorem hillComplexFreeSupportedPeriodMap_zero_iff_periods (n : ℕ) (hn : 1≤n)
    (ε D : ℝ) (hD : 0≤D) (hc : HillComplexPeriodControl hq hr ε D)
    (a : PositiveDeletedCoeff 2 (n : ℤ)) (p : Coeff 2) (hp : p∈ball 0 ε) :
    hillComplexFreeSupportedPeriodMap hq hr n (a,p)=0 ↔
      ∀ k : ℕ, 1≤k → k≠n → hillAbelianComplexPeriod 0 hq hr n k ((a : Coeff 2),p)=0 := by
  constructor
  · intro hzero k hk hkn
    have hh := congrArg (fun b : PositiveDeletedCoeff 2 (n : ℤ) => (b : Coeff 2) (k : ℤ)) hzero
    change (hillComplexFreeSupportedPeriodMap hq hr n (a,p) : Coeff 2) (k : ℤ)=0 at hh
    rw [hillComplexFreeSupportedPeriodMap_apply_on hq hr n hn ε D hD hc a p hp (k : ℤ),
      hillComplexScaledPeriodCoordinate,if_pos (by constructor <;> omega),Int.toNat_natCast] at hh
    apply (mul_eq_zero.mp hh).resolve_left
    apply div_ne_zero
    · exact sub_ne_zero.mpr (Complex.ofReal_injective.ne (strictMono_freeHillValue.injective.ne hkn))
    · exact Nat.cast_ne_zero.mpr (show n≠0 by omega)
  · intro hperiod
    apply Subtype.ext
    apply lp.ext
    funext m
    change (hillComplexFreeSupportedPeriodMap hq hr n (a,p) : Coeff 2) m=0
    rw [hillComplexFreeSupportedPeriodMap_apply_on hq hr n hn ε D hD hc a p hp m,
      hillComplexScaledPeriodCoordinate]
    by_cases hm : 0<m ∧ m≠(n : ℤ)
    · rw [if_pos hm,hperiod m.toNat (by omega) (by omega),mul_zero]
    · rw [if_neg hm]

end NLS.KdV
