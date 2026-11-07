import NLS.KdV.HillEnergyAffineParameters
import NLS.KdV.HillEnergyNumeratorPeriods

/-! A single entire contour-period functional of affine coefficient
pairs supplies the actual escaping-index period and filled column limits.
Every contour retains its literal physical normalization and root. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillAffineEnergyPeriodIntegrand (c : ℂ) (ψ : CoeffPair 2) (t : ℂ × (Coeff 2 × Coeff 2)) : ℂ :=
  (2*t.1*hillAffineEnergyProduct (t.1^2-c,t.2))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ t.1

def hillAffineEnergyPeriod (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) (t : Coeff 2 × Coeff 2) : ℂ :=
  (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),hillAffineEnergyPeriodIntegrand c ψ (z,t))

def hillEnergyFullProductFixedPeriod (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) (d : lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  hillAffineEnergyPeriod c ψ D (hillFullEnergyProductParameters d)

def hillEnergyFullProductPeriodColumn (m : ℕ+) (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) (d : lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  hillEnergyFullProductFixedPeriod c ψ D (hillZeroCoordinateShift m d 1)-hillEnergyFullProductFixedPeriod c ψ D d

theorem analyticOnNhd_hillAffineEnergyPeriodIntegrand (c : ℂ) (ψ : CoeffPair 2) :
    AnalyticOnNhd ℂ (hillAffineEnergyPeriodIntegrand c ψ)
      (sourceCanonicalRootDomain (by norm_num) (by norm_num) ψ ×ˢ univ) := by
  intro t ht
  have hp := (analyticAt_hillAffineEnergyProduct (t.1^2-c,t.2)).comp
    (f := fun s : ℂ × (Coeff 2 × Coeff 2) => (s.1^2-c,s.2))
    (((analyticAt_fst.pow 2).sub analyticAt_const).prod analyticAt_snd)
  exact ((analyticAt_const.mul analyticAt_fst).mul hp).div
    ((sourceCanonicalRoot_analyticOnNhd (by norm_num) (by norm_num) ψ t.1 ht.1).comp
      (f := Prod.fst) analyticAt_fst)
    (sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) ψ t.1 ht.1)

theorem analyticOnNhd_hillAffineEnergyPeriod (c : ℂ) (ψ : CoeffPair 2)
    (hreal : IsRealType (CoeffPair.toMax 2 ψ)) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) :
    AnalyticOnNhd ℂ (hillAffineEnergyPeriod c ψ D) univ := by
  have h := analyticOnNhd_circleIntegral_of_jointAnalytic (hillAffineEnergyPeriodIntegrand c ψ)
    ((isOpen_sourceCanonicalRootDomain_of_realType (by norm_num) (by norm_num) ψ hreal).prod isOpen_univ)
    (analyticOnNhd_hillAffineEnergyPeriodIntegrand c ψ) (D.center:ℂ) D.radius D.radius_pos.le
    isOpen_univ (fun t _ z hz => ⟨D.sphere_subset_rootDomain hz,mem_univ t⟩)
  intro t ht
  exact analyticAt_const.mul (h t ht)

theorem analyticOnNhd_hillEnergyFullProductFixedPeriod (c : ℂ) (ψ : CoeffPair 2)
    (hreal : IsRealType (CoeffPair.toMax 2 ψ)) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) :
    AnalyticOnNhd ℂ (hillEnergyFullProductFixedPeriod c ψ D) univ := by
  intro d _
  exact (analyticOnNhd_hillAffineEnergyPeriod c ψ hreal D _ (mem_univ _)).comp
    (analyticAt_hillFullEnergyProductParameters d)

theorem hillEnergyProductFixedPeriod_eq_affinePeriod (n : ℕ+) (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergyProductFixedPeriod n c ψ D d = hillAffineEnergyPeriod c ψ D (hillDeletedEnergyProductParameters n d) := by
  unfold hillEnergyProductFixedPeriod hillAffineEnergyPeriod
  apply congrArg (fun w : ℂ => (2*Real.pi:ℂ)⁻¹*w)
  apply circleIntegral.integral_congr D.radius_pos.le
  intro z _
  unfold hillEnergyProductPeriodIntegrand hillAffineEnergyPeriodIntegrand
  dsimp only
  rw [hillEnergySequenceProduct_eq_affine]

theorem hillEnergyFullProductFixedPeriod_eq_numeratorPeriod (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergyFullProductFixedPeriod c ψ D d = hillEnergyNumeratorPeriod c ψ D
      (fun E => hillEnergySequenceFullProduct (E,d)) := by
  unfold hillEnergyFullProductFixedPeriod hillAffineEnergyPeriod hillEnergyNumeratorPeriod
  apply congrArg (fun w : ℂ => (2*Real.pi:ℂ)⁻¹*w)
  apply circleIntegral.integral_congr D.radius_pos.le
  intro z _
  unfold hillAffineEnergyPeriodIntegrand
  dsimp only
  rw [hillEnergySequenceFullProduct_eq_affine]


theorem hillEnergyFullProductFixedPeriod_coordinate_affine (m : ℕ+) (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (w : ℂ) :
    hillEnergyFullProductFixedPeriod c ψ D (hillZeroCoordinateShift m d w) =
      hillEnergyFullProductFixedPeriod c ψ D d+w*hillEnergyFullProductPeriodColumn m c ψ D d := by
  have hA : AnalyticOnNhd ℂ (fun E => hillEnergySequenceFullProduct (E,d)) univ := by
    intro E _
    exact (analyticAt_hillEnergySequenceFullProduct (E,d)).comp
      (f := fun z : ℂ => (z,d)) (analyticAt_id.prod analyticAt_const)
  have hB : AnalyticOnNhd ℂ (fun E => hillEnergySequenceFullProduct (E,hillZeroCoordinateShift m d 1)) univ := by
    intro E _
    exact (analyticAt_hillEnergySequenceFullProduct (E,hillZeroCoordinateShift m d 1)).comp
      (f := fun z : ℂ => (z,hillZeroCoordinateShift m d 1)) (analyticAt_id.prod analyticAt_const)
  have he : (fun E => hillEnergySequenceFullProduct (E,hillZeroCoordinateShift m d w)) =
      (fun E => hillEnergySequenceFullProduct (E,d)+w*(hillEnergySequenceFullProduct (E,hillZeroCoordinateShift m d 1)-
        hillEnergySequenceFullProduct (E,d))) := funext (fun E => hillEnergySequenceFullProduct_coordinate_affine m E d w)
  simp_rw [hillEnergyFullProductPeriodColumn,hillEnergyFullProductFixedPeriod_eq_numeratorPeriod]
  rw [he]
  unfold hillEnergyNumeratorPeriod
  have hi : (fun z => (2*z*(hillEnergySequenceFullProduct (z^2-c,d)+w*(
      hillEnergySequenceFullProduct (z^2-c,hillZeroCoordinateShift m d 1)-hillEnergySequenceFullProduct (z^2-c,d))))/
        sourceCanonicalRoot (by norm_num) (by norm_num) ψ z) =
      (fun z => (2*z*hillEnergySequenceFullProduct (z^2-c,d))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z+
        w*((2*z*hillEnergySequenceFullProduct (z^2-c,hillZeroCoordinateShift m d 1))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z-
          (2*z*hillEnergySequenceFullProduct (z^2-c,d))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)) := by
    funext z
    ring
  rw [hi]
  have h0 := circleIntegrable_hillEnergyNumerator c ψ D _ hA
  have h1 := circleIntegrable_hillEnergyNumerator c ψ D _ hB
  have hw : CircleIntegrable (fun z => w*((2*z*hillEnergySequenceFullProduct (z^2-c,hillZeroCoordinateShift m d 1))/
      sourceCanonicalRoot (by norm_num) (by norm_num) ψ z-
      (2*z*hillEnergySequenceFullProduct (z^2-c,d))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z))
      (D.center:ℂ) D.radius := (h1.sub h0).const_mul w
  rw [circleIntegral.integral_add h0 hw,circleIntegral.integral_const_mul,
    circleIntegral.integral_sub h1 h0]
  ring

theorem hasDerivAt_hillEnergyFullProductFixedPeriod_coordinate (m : ℕ+) (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (w : ℂ) :
    HasDerivAt (fun z : ℂ => hillEnergyFullProductFixedPeriod c ψ D (hillZeroCoordinateShift m d z))
      (hillEnergyFullProductPeriodColumn m c ψ D d) w := by
  have he := funext (hillEnergyFullProductFixedPeriod_coordinate_affine m c ψ D d)
  rw [he]
  simpa only [zero_add,one_mul,id_eq] using! (hasDerivAt_const w (hillEnergyFullProductFixedPeriod c ψ D d)).add
    ((hasDerivAt_id w).mul_const (hillEnergyFullProductPeriodColumn m c ψ D d))


theorem fderiv_hillEnergyFullProductFixedPeriod_coordinate (m : ℕ+) (c : ℂ) (ψ : CoeffPair 2)
    (hreal : IsRealType (CoeffPair.toMax 2 ψ)) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    fderiv ℂ (hillEnergyFullProductFixedPeriod c ψ D) d (lp.single 2 m 1) =
      hillEnergyFullProductPeriodColumn m c ψ D d := by
  have hp := (analyticOnNhd_hillEnergyFullProductFixedPeriod c ψ hreal D d (mem_univ d)).differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun w : ℂ => hillZeroCoordinateShift m d w) (lp.single 2 m 1 : lp (fun _ : ℕ+ => ℂ) 2) 0 := by
    simpa only [hillZeroCoordinateShift,zero_add,one_smul] using!
      (hasDerivAt_const (0:ℂ) d).add ((hasDerivAt_id (0:ℂ)).smul_const (lp.single 2 m 1 : lp (fun _ : ℕ+ => ℂ) 2))
  have hc := hp.comp_hasDerivAt_of_eq 0 hline (by simp [hillZeroCoordinateShift])
  exact hc.unique (hasDerivAt_hillEnergyFullProductFixedPeriod_coordinate m c ψ D d 0)

theorem tendsto_hillEnergyProductFixedPeriod_escaping
    (c : ℂ) (ψ : CoeffPair 2) (hreal : IsRealType (CoeffPair.toMax 2 ψ)) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (d : ℕ → lp (fun _ : ℕ+ => ℂ) 2) (d₀ : lp (fun _ : ℕ+ => ℂ) 2) (hd : Tendsto d atTop (𝓝 d₀)) :
    Tendsto (fun j => hillEnergyProductFixedPeriod (n j) c ψ D (d j)) atTop
      (𝓝 (hillEnergyFullProductFixedPeriod c ψ D d₀)) := by
  simp_rw [hillEnergyProductFixedPeriod_eq_affinePeriod]
  exact (analyticOnNhd_hillAffineEnergyPeriod c ψ hreal D _ (mem_univ _)).continuousAt.tendsto.comp
    (tendsto_hillDeletedEnergyProductParameters n hn d d₀ hd)

theorem tendsto_hillEnergyProductPeriodColumn_escaping (m : ℕ+)
    (c : ℂ) (ψ : CoeffPair 2) (hreal : IsRealType (CoeffPair.toMax 2 ψ)) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (d : ℕ → lp (fun _ : ℕ+ => ℂ) 2) (d₀ : lp (fun _ : ℕ+ => ℂ) 2) (hd : Tendsto d atTop (𝓝 d₀)) :
    Tendsto (fun j => hillEnergyProductPeriodColumn (n j) m c ψ D (d j)) atTop
      (𝓝 (hillEnergyFullProductPeriodColumn m c ψ D d₀)) := by
  have hs : Tendsto (fun j => hillZeroCoordinateShift m (d j) 1) atTop (𝓝 (hillZeroCoordinateShift m d₀ 1)) := by
    simpa only [hillZeroCoordinateShift,one_smul] using hd.add_const (lp.single 2 m 1)
  simp_rw [hillEnergyProductPeriodColumn_eq_difference]
  exact (tendsto_hillEnergyProductFixedPeriod_escaping c ψ hreal D n hn _ _ hs).sub
    (tendsto_hillEnergyProductFixedPeriod_escaping c ψ hreal D n hn d d₀ hd)

end NLS.KdV
