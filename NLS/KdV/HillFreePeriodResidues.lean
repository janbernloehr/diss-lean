import NLS.KdV.HillFreeEnergyProduct
import NLS.KdV.HillProductFixedPeriods

/-! Free Hill periods on ANY genuine positive free period circle.
The residues use the actual canonical root sign and literal 1/(2*pi). -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillFree_periodCircle_point_ne (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ))
    (j : ℤ) (z : ℂ) (hz : z ∈ sphere (D.center:ℂ) D.radius) : z ≠ (Real.pi:ℂ)*j := by
  have h := D.sphere_subset_rootDomain hz j
  simpa only [sourcePeriodicSegment_zero_source,mem_singleton_iff] using h

theorem hillFree_periodCircle_pole_integral (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ)) (j : ℤ) :
    (∮ z in C((D.center:ℂ),D.radius),(z-(Real.pi:ℂ)*j)⁻¹) =
      if ((m:ℕ):ℤ) = j then 2*Real.pi*I else 0 := by
  by_cases h : ((m:ℕ):ℤ) = j
  · rw [if_pos h]
    apply circleIntegral.integral_sub_inv_of_mem_ball
    apply D.gap
    rw [sourcePeriodicSegment_zero_source,h]
    exact mem_singleton _
  · rw [if_neg h]
    have hdiff : DifferentiableOn ℂ (fun z : ℂ => (z-(Real.pi:ℂ)*j)⁻¹)
        (closedBall (D.center:ℂ) D.radius) := by
      intro z hz
      have havoid := D.closedBall_subset_omittedDomain hz j (Ne.symm h)
      have hzne : z ≠ (Real.pi:ℂ)*j := by
        simpa only [sourcePeriodicSegment_zero_source,mem_singleton_iff] using havoid
      have hf : DifferentiableAt ℂ (fun w : ℂ => w-(Real.pi:ℂ)*j) z := by fun_prop
      exact (hf.inv (sub_ne_zero.mpr hzne)).differentiableWithinAt
    exact (hdiff.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero D.radius_pos.le

theorem hillFree_periodCircle_inverse_integrable (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ)) (j : ℤ) :
    CircleIntegrable (fun z : ℂ => (z-(Real.pi:ℂ)*j)⁻¹) (D.center:ℂ) D.radius := by
  apply ContinuousOn.circleIntegrable D.radius_pos.le
  apply ContinuousOn.inv₀
  · exact continuousOn_id.sub continuousOn_const
  · intro z hz
    exact sub_ne_zero.mpr (hillFree_periodCircle_point_ne m D j z hz)

theorem hillFree_quadratic_kernel_integral (m r : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ)) :
    (∮ z in C((D.center:ℂ),D.radius),I/(((Real.pi:ℂ)*(r:ℕ))^2-z^2)) =
      if m = r then ((r:ℕ):ℂ)⁻¹ else 0 := by
  let a : ℂ := (Real.pi:ℂ)*(r:ℕ)
  have ha : a ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast r.ne_zero)
  have heq : (∮ z in C((D.center:ℂ),D.radius),I/(a^2-z^2)) =
      -(I/(2*a))*((∮ z in C((D.center:ℂ),D.radius),(z-a)⁻¹)-
        ∮ z in C((D.center:ℂ),D.radius),(z-(-a))⁻¹) := by
    have hpoint (z : ℂ) (hz : z ∈ sphere (D.center:ℂ) D.radius) :
        I/(a^2-z^2) = -(I/(2*a))*((z-a)⁻¹-(z-(-a))⁻¹) := by
      have hd := hillFree_energy_denominator_ne_zero r z (D.sphere_subset_rootDomain hz)
      have hp := sub_ne_zero.mpr (hillFree_periodCircle_point_ne m D ((r:ℕ):ℤ) z hz)
      simp only [Int.cast_natCast] at hp
      change z-a ≠ 0 at hp
      change a^2-z^2 ≠ 0 at hd
      have hn : z-(-a) ≠ 0 := by
        have hh := hillFree_periodCircle_point_ne m D (-((r:ℕ):ℤ)) z hz
        simpa only [Int.cast_neg,Int.cast_natCast,mul_neg,a] using sub_ne_zero.mpr hh
      change I/(a^2-z^2) = _
      field_simp [ha,hd,hp,hn]
      ring
    rw [circleIntegral.integral_congr D.radius_pos.le hpoint,circleIntegral.integral_const_mul]
    have hp := hillFree_periodCircle_inverse_integrable m D ((r:ℕ):ℤ)
    have hn := hillFree_periodCircle_inverse_integrable m D (-((r:ℕ):ℤ))
    simp only [Int.cast_neg,Int.cast_natCast,mul_neg] at hp hn
    rw [circleIntegral.integral_sub hp hn]
  change (∮ z in C((D.center:ℂ),D.radius),I/(a^2-z^2)) = _
  rw [heq]
  have hneg : ((m:ℕ):ℤ) ≠ -((r:ℕ):ℤ) := by
    have hm : 0 < ((m:ℕ):ℤ) := by exact_mod_cast m.pos
    have hr : 0 < ((r:ℕ):ℤ) := by exact_mod_cast r.pos
    omega
  have he : ((m:ℕ):ℤ) = ((r:ℕ):ℤ) ↔ m = r := by
    constructor
    · exact fun h => Subtype.ext (Int.ofNat.inj h)
    · exact fun h => congrArg (fun k : ℕ+ => ((k:ℕ):ℤ)) h
  have hp := hillFree_periodCircle_pole_integral m D ((r:ℕ):ℤ)
  have hn := hillFree_periodCircle_pole_integral m D (-((r:ℕ):ℤ))
  simp only [Int.cast_natCast,Int.cast_neg,mul_neg,he,if_neg hneg] at hp hn
  change (∮ z in C((D.center:ℂ),D.radius),(z-a)⁻¹) = _ at hp
  change (∮ z in C((D.center:ℂ),D.radius),(z-(-a))⁻¹) = _ at hn
  rw [hp,hn,sub_zero]
  by_cases hmr : m = r
  · rw [if_pos hmr,if_pos hmr]
    dsimp only [a]
    have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hr : ((r:ℕ):ℂ) ≠ 0 := by exact_mod_cast r.ne_zero
    field_simp
    ring_nf
    simp [I_sq]
  · simp only [if_neg hmr,mul_zero]

theorem hillEnergyProductFixedPeriod_free (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ)) :
    hillEnergyProductFixedPeriod n 0 (0:CoeffPair 2) D 0 =
      if m = n then (Real.pi:ℂ)*(n:ℕ)/2 else 0 := by
  have hpoint (z : ℂ) (hz : z ∈ sphere (D.center:ℂ) D.radius) :
      hillEnergyProductPeriodIntegrand n 0 (0:CoeffPair 2) (z,0) =
        ((Real.pi:ℂ)*(n:ℕ))^2*(I/(((Real.pi:ℂ)*(n:ℕ))^2-z^2)) := by
    unfold hillEnergyProductPeriodIntegrand
    dsimp only
    rw [sub_zero,hillEnergyProductPeriodIntegrand_free n z (D.sphere_subset_rootDomain hz)]
    ring
  unfold hillEnergyProductFixedPeriod
  rw [circleIntegral.integral_congr D.radius_pos.le hpoint,circleIntegral.integral_const_mul,
    hillFree_quadratic_kernel_integral]
  by_cases hmn : m = n
  · rw [if_pos hmn,if_pos hmn]
    have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hn : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
    field_simp
  · simp only [if_neg hmn,mul_zero]

end NLS.KdV
