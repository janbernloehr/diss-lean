import NLS.KdV.HillProductCoordinateVariation
import NLS.ZakharovShabat.SourceCanonicalRootProduct
import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! Literal normalized Hill product periods on ACTUAL fixed Dirac
frequency circles. At a fixed real source these are entire functions
of the full inverse-index l2 zero data. Their coordinate derivatives
are the corresponding filled product-derivative periods. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillEnergyProductPeriodIntegrand (n : ℕ+) (c : ℂ) (ψ : CoeffPair 2)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  (2*t.1*hillEnergySequenceProduct n (t.1^2-c,t.2))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ t.1

theorem analyticOnNhd_hillEnergyProductPeriodIntegrand (n : ℕ+) (c : ℂ) (ψ : CoeffPair 2) :
    AnalyticOnNhd ℂ (hillEnergyProductPeriodIntegrand n c ψ)
      (sourceCanonicalRootDomain (by norm_num) (by norm_num) ψ ×ˢ univ) := by
  intro t ht
  have hP := (analyticAt_hillEnergySequenceProduct n (t.1^2-c,t.2)).comp
    (f := fun s : ℂ × lp (fun _ : ℕ+ => ℂ) 2 => (s.1^2-c,s.2))
    (((analyticAt_fst.pow 2).sub analyticAt_const).prod analyticAt_snd)
  have hroot := (sourceCanonicalRoot_analyticOnNhd (by norm_num) (by norm_num) ψ t.1 ht.1).comp
    (f := Prod.fst) analyticAt_fst
  exact ((analyticAt_const.mul analyticAt_fst).mul hP).div hroot
    (sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) ψ t.1 ht.1)

def hillEnergyProductFixedPeriod (n : ℕ+) (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d : lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),hillEnergyProductPeriodIntegrand n c ψ (z,d))

theorem analyticOnNhd_hillEnergyProductFixedPeriod (n : ℕ+) (c : ℂ) (ψ : CoeffPair 2)
    (hreal : IsRealType (CoeffPair.toMax 2 ψ)) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) :
    AnalyticOnNhd ℂ (hillEnergyProductFixedPeriod n c ψ D) univ := by
  have h := analyticOnNhd_circleIntegral_of_jointAnalytic (hillEnergyProductPeriodIntegrand n c ψ)
    ((isOpen_sourceCanonicalRootDomain_of_realType (by norm_num) (by norm_num) ψ hreal).prod isOpen_univ)
    (analyticOnNhd_hillEnergyProductPeriodIntegrand n c ψ) (D.center:ℂ) D.radius D.radius_pos.le
    isOpen_univ (fun d _ z hz => ⟨D.sphere_subset_rootDomain hz,mem_univ d⟩)
  intro d hd
  exact analyticAt_const.mul (h d hd)

theorem circleIntegrable_hillEnergyProductPeriodIntegrand (n : ℕ+) (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    CircleIntegrable (fun z : ℂ => hillEnergyProductPeriodIntegrand n c ψ (z,d)) (D.center:ℂ) D.radius := by
  apply ContinuousOn.circleIntegrable D.radius_pos.le
  intro z hz
  exact ((analyticOnNhd_hillEnergyProductPeriodIntegrand n c ψ (z,d)
    ⟨D.sphere_subset_rootDomain hz,mem_univ d⟩).comp (f := fun w : ℂ => (w,d))
      (analyticAt_id.prod analyticAt_const)).continuousAt.continuousWithinAt

theorem hillEnergyProductFixedPeriod_coordinate_affine (n m : ℕ+) (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (w : ℂ) :
    hillEnergyProductFixedPeriod n c ψ D (hillZeroCoordinateShift m d w) =
      hillEnergyProductFixedPeriod n c ψ D d+w*(
        hillEnergyProductFixedPeriod n c ψ D (hillZeroCoordinateShift m d 1)-hillEnergyProductFixedPeriod n c ψ D d) := by
  have hi (z : ℂ) : hillEnergyProductPeriodIntegrand n c ψ (z,hillZeroCoordinateShift m d w) =
      hillEnergyProductPeriodIntegrand n c ψ (z,d)+w*(
        hillEnergyProductPeriodIntegrand n c ψ (z,hillZeroCoordinateShift m d 1)-
          hillEnergyProductPeriodIntegrand n c ψ (z,d)) := by
    unfold hillEnergyProductPeriodIntegrand
    dsimp only
    rw [hillEnergySequenceProduct_coordinate_affine]
    unfold hillEnergyProductCoordinateDerivative
    ring
  have h0 := circleIntegrable_hillEnergyProductPeriodIntegrand n c ψ D d
  have h1 := circleIntegrable_hillEnergyProductPeriodIntegrand n c ψ D (hillZeroCoordinateShift m d 1)
  have hw : CircleIntegrable (fun z : ℂ => w*(hillEnergyProductPeriodIntegrand n c ψ (z,hillZeroCoordinateShift m d 1)-
      hillEnergyProductPeriodIntegrand n c ψ (z,d))) (D.center:ℂ) D.radius := (h1.sub h0).const_mul w
  unfold hillEnergyProductFixedPeriod
  simp_rw [hi]
  rw [circleIntegral.integral_add h0 hw,circleIntegral.integral_const_mul,
    circleIntegral.integral_sub h1 h0]
  ring

def hillEnergyProductPeriodColumn (n m : ℕ+) (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d : lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
    (2*z*hillEnergyProductCoordinateDerivative n m (z^2-c,d))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)

theorem hillEnergyProductPeriodColumn_eq_difference (n m : ℕ+) (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergyProductPeriodColumn n m c ψ D d =
      hillEnergyProductFixedPeriod n c ψ D (hillZeroCoordinateShift m d 1)-hillEnergyProductFixedPeriod n c ψ D d := by
  have h0 := circleIntegrable_hillEnergyProductPeriodIntegrand n c ψ D d
  have h1 := circleIntegrable_hillEnergyProductPeriodIntegrand n c ψ D (hillZeroCoordinateShift m d 1)
  unfold hillEnergyProductPeriodColumn hillEnergyProductFixedPeriod
  rw [← mul_sub,← circleIntegral.integral_sub h1 h0]
  congr 1
  apply circleIntegral.integral_congr D.radius_pos.le
  intro z _
  unfold hillEnergyProductPeriodIntegrand hillEnergyProductCoordinateDerivative
  dsimp only
  ring

theorem hasDerivAt_hillEnergyProductFixedPeriod_coordinate (n m : ℕ+) (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (w : ℂ) :
    HasDerivAt (fun z : ℂ => hillEnergyProductFixedPeriod n c ψ D (hillZeroCoordinateShift m d z))
      (hillEnergyProductPeriodColumn n m c ψ D d) w := by
  rw [hillEnergyProductPeriodColumn_eq_difference]
  have he := funext (hillEnergyProductFixedPeriod_coordinate_affine n m c ψ D d)
  rw [he]
  simpa only [zero_add,one_mul,id_eq] using!
    (hasDerivAt_const w (hillEnergyProductFixedPeriod n c ψ D d)).add
      ((hasDerivAt_id w).mul_const (hillEnergyProductFixedPeriod n c ψ D (hillZeroCoordinateShift m d 1)-
        hillEnergyProductFixedPeriod n c ψ D d))

theorem fderiv_hillEnergyProductFixedPeriod_coordinate (n m : ℕ+) (c : ℂ) (ψ : CoeffPair 2)
    (hreal : IsRealType (CoeffPair.toMax 2 ψ)) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    fderiv ℂ (hillEnergyProductFixedPeriod n c ψ D) d (lp.single 2 m 1) =
      hillEnergyProductPeriodColumn n m c ψ D d := by
  have hline : HasDerivAt (hillZeroCoordinateShift m d)
      (lp.single 2 m 1 : lp (fun _ : ℕ+ => ℂ) 2) 0 := by
    simpa only [hillZeroCoordinateShift,zero_add,one_smul] using!
      (hasDerivAt_const (0:ℂ) d).add ((hasDerivAt_id (0:ℂ)).smul_const
        (lp.single 2 m 1 : lp (fun _ : ℕ+ => ℂ) 2))
  have hF : HasFDerivAt (hillEnergyProductFixedPeriod n c ψ D)
      (fderiv ℂ (hillEnergyProductFixedPeriod n c ψ D) d) (hillZeroCoordinateShift m d 0) := by
    simpa only [hillZeroCoordinateShift,zero_smul,add_zero] using
      (analyticOnNhd_hillEnergyProductFixedPeriod n c ψ hreal D d (mem_univ _)).differentiableAt.hasFDerivAt
  have hc := hF.comp_hasDerivAt 0 hline
  dsimp only [Function.comp_def] at hc
  exact hc.unique (hasDerivAt_hillEnergyProductFixedPeriod_coordinate n m c ψ D d 0)

end NLS.KdV
