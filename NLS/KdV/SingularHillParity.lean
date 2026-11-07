import NLS.Fourier.PeriodicParityProjection
import NLS.KdV.SingularHillRieszDomain

/-! Original native Hill pencils and resolvents preserve BOTH parities for
potentials with physical period one, with no real-potential assumption. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- Domain inclusion commutes with the SAME raw parity masks. -/
theorem singularHillDomainInclusion_parity (r : ℤ) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillDomainInclusion (periodicParityProjection 1 2 r f)=
      periodicParityProjection (-1) 2 r (singularHillDomainInclusion f) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [singularHillDomainInclusion_coefficient,periodicParityProjection_coefficient,
    periodicParityProjection_coefficient,singularHillDomainInclusion_coefficient]

/-- The actual singular native operator commutes with parity for every
potential with vanishing odd original Fourier coefficients. -/
theorem singularHillOperator_parity (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : ∀ k : ℤ, k%2 ≠ 0 → q.val (mode (-k))=0) (r : ℤ) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillOperator q (periodicParityProjection 1 2 r f)=
      periodicParityProjection (-1) 2 r (singularHillOperator q f) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [singularHillOperator_coefficient,periodicParityProjection_coefficient,
    periodicParityProjection_coefficient,singularHillOperator_coefficient]
  have hsum : (∑' m : ℤ, q.val (mode (-(k-m)))*(periodicParityProjection 1 2 r f).val (mode (-m))) =
      if k%2=r%2 then ∑' m : ℤ, q.val (mode (-(k-m)))*f.val (mode (-m)) else 0 := by
    by_cases hk : k%2=r%2
    · rw [if_pos hk]
      apply tsum_congr
      intro m
      rw [periodicParityProjection_coefficient]
      by_cases hm : m%2=r%2
      · rw [if_pos hm]
      · rw [if_neg hm,hq (k-m) (by omega)]
        simp only [zero_mul,mul_zero]
    · rw [if_neg hk]
      suffices hzero : ∀ m : ℤ, q.val (mode (-(k-m)))*(periodicParityProjection 1 2 r f).val (mode (-m))=0 by
        simp only [hzero,tsum_zero]
      intro m
      rw [periodicParityProjection_coefficient]
      by_cases hm : m%2=r%2
      · rw [if_pos hm,hq (k-m) (by omega),zero_mul]
      · rw [if_neg hm,mul_zero]
  rw [hsum]
  split_ifs <;> simp

/-- The ENTIRE native pencil respects parity on its original H1 domain. -/
theorem singularHillPencil_parity (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : ∀ k : ℤ, k%2 ≠ 0 → q.val (mode (-k))=0) (z : ℂ) (r : ℤ) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    (singularHillOperator q-z • singularHillDomainInclusion) (periodicParityProjection 1 2 r f)=
      periodicParityProjection (-1) 2 r ((singularHillOperator q-z • singularHillDomainInclusion) f) := by
  change singularHillOperator q (periodicParityProjection 1 2 r f)-z • singularHillDomainInclusion (periodicParityProjection 1 2 r f)=_
  rw [singularHillOperator_parity q hq,singularHillDomainInclusion_parity]
  change _ = periodicParityProjection (-1) 2 r (singularHillOperator q f-z • singularHillDomainInclusion f)
  rw [map_sub,map_smul]

/-- The SAME actual full-base H1-valued resolvent preserves both parities. -/
theorem singularHillResolventToH1_parity (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : ∀ k : ℤ, k%2 ≠ 0 → q.val (mode (-k))=0) (z : ℂ) (hz : z ∈ singularHillResolventSet q)
    (r : ℤ) (F : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    periodicParityProjection 1 2 r (singularHillResolventToH1 q z F)=
      singularHillResolventToH1 q z (periodicParityProjection (-1) 2 r F) := by
  apply hz.1
  rw [singularHillPencil_parity q hq]
  change periodicParityProjection (-1) 2 r
    (singularHillOperator q (singularHillResolventToH1 q z F)-z • singularHillDomainInclusion (singularHillResolventToH1 q z F))=
      singularHillOperator q (singularHillResolventToH1 q z (periodicParityProjection (-1) 2 r F))-
        z • singularHillDomainInclusion (singularHillResolventToH1 q z (periodicParityProjection (-1) 2 r F))
  rw [singularHillResolventToH1_right q z hz,singularHillResolventToH1_right q z hz]

/-- The actual native H1 contour lift preserves parity on its FULL original base. -/
theorem singularHillRieszToH1_parity (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : ∀ k : ℤ, k%2 ≠ 0 → q.val (mode (-k))=0) (c : ℂ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hc : sphere c rho ⊆ singularHillResolventSet q) (r : ℤ) (F : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    periodicParityProjection 1 2 r (singularHillRieszToH1 q c rho F)=
      singularHillRieszToH1 q c rho (periodicParityProjection (-1) 2 r F) := by
  have hcont : ContinuousOn (fun z => -singularHillResolventToH1 q z) (sphere c rho) :=
    fun z hz => ((analyticAt_singularHillResolventToH1 q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hint : CircleIntegrable (fun z => -(singularHillResolventToH1 q z F)) c rho :=
    (hcont.clm_apply continuousOn_const).circleIntegrable hrho
  rw [singularHillRieszToH1_apply q c rho hrho hc,map_smul,
    CircleIntegral.map (periodicParityProjection 1 2 r) hint,singularHillRieszToH1_apply q c rho hrho hc]
  congr 1
  apply circleIntegral.integral_congr hrho
  intro z hz
  dsimp only
  rw [map_neg,singularHillResolventToH1_parity q hq z (hc hz)]

end NLS.KdV
