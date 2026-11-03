import NLS.KdV.HillHminusOneDiscriminant
import NLS.KdV.HillMiuraL2PhysicalQuasi
import NLS.MKdV.L2QuasiHillUniqueness

/-! # Actual rough quasi-derivative monodromy behind the H^-1 discriminant

Every analytic shifted-Miura chart gives an actual physical L2 profile
and a unique absolutely continuous initial-value solution. Its trace is
the intrinsic H^-1 discriminant, with the exact constant energy shift.
The Fourier identity fixes the distributional potential without changing
its normalization. A chart-independent singular Hill operator domain and
its self-adjoint spectral realization are not asserted here.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV.HillHminusMiuraChart

def physicalProfile (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) : IntervalL2 :=
  unitL2SynthesisEquiv (C.lift q)

def physicalSolution (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (lambda : ℂ) (v : ℂ × ℂ) :
    Curve (ℂ × ℂ) := l2QuasiHillSolution (C.physicalProfile q) (lambda+C.energyShift) v

/-- The profile has the original period-one Fourier coefficients. -/
theorem physicalProfile_coefficient (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (k : ℤ) :
    intervalFourierCoefficient 1 (C.physicalProfile q) k = C.lift q k :=
  unitL2SynthesisLinear_coefficient (C.lift q) k

/-- The physical profile's distributional Miura image is exactly q plus
the chart's constant energy translation, in the original Fourier scale. -/
theorem physicalProfile_Miura_coefficient (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hq : q ∈ C.domain) (k : ℤ) :
    q.val k = 2*I*(Real.pi : ℂ)*k*intervalFourierCoefficient 1 (C.physicalProfile q) k+
      (∑' j : ℤ, intervalFourierCoefficient 1 (C.physicalProfile q) (k-j)*
        intervalFourierCoefficient 1 (C.physicalProfile q) j)-
          if k = 0 then C.energyShift else 0 := by
  simp only [physicalProfile_coefficient]
  have he := congrArg (fun p : PeriodOneHminusOne => p.val k) (C.image q hq)
  change (periodOneMiura (C.lift q)).val k = q.val k+(periodOneL2Inclusion (lp.single 2 0 C.energyShift)).val k at he
  rw [periodOneMiura_apply,periodOneL2Inclusion_apply] at he
  by_cases hk : k = 0 <;> simp [lp.single_apply,hk] at he ⊢ <;> linear_combination -he

@[simp] theorem physicalSolution_zero (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (lambda : ℂ) (v : ℂ × ℂ) : C.physicalSolution q lambda v ⟨0,by constructor <;> norm_num⟩ = v :=
  l2QuasiHillSolution_zero _ _ _

theorem physicalSolution_eq_integral (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (lambda : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    C.physicalSolution q lambda v t = v+∫ s in (0 : ℝ)..t.val,
      quasiHillCoefficient (C.physicalProfile q s) (lambda+C.energyShift) (extend (C.physicalSolution q lambda v) s) :=
  l2QuasiHillSolution_eq_integral _ _ _ _

theorem physicalSolution_unique_integral (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (lambda : ℂ) (v : ℂ × ℂ) (w : Curve (ℂ × ℂ))
    (hw : ∀ t : Icc (0 : ℝ) 1, w t = v+∫ s in (0 : ℝ)..t.val,
      quasiHillCoefficient (C.physicalProfile q s) (lambda+C.energyShift) (extend w s)) :
    w = C.physicalSolution q lambda v := l2QuasiHillSolution_unique_integral _ _ _ w hw

theorem absolutelyContinuous_physicalSolution (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (lambda : ℂ) (v : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (extend (C.physicalSolution q lambda v)) 0 1 :=
  absolutelyContinuousOnInterval_l2QuasiHillSolution _ _ _

theorem ae_hasDerivAt_physicalSolution (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (lambda : ℂ) (v : ℂ × ℂ) :
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (C.physicalSolution q lambda v))
        (quasiHillCoefficient (C.physicalProfile q s) (lambda+C.energyShift) (extend (C.physicalSolution q lambda v) s)) s :=
  ae_hasDerivAt_l2QuasiHillSolution _ _ _

theorem analyticOnNhd_physicalSolution (C : HillHminusMiuraChart) (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun p : ℂ × PeriodOneHminusOne => C.physicalSolution p.2 p.1 v)
      (univ ×ˢ C.domain) := by
  intro p hp
  have hu : AnalyticAt ℂ (fun p : ℂ × PeriodOneHminusOne => C.physicalProfile p.2) p :=
    (unitL2SynthesisEquiv.toContinuousLinearEquiv.analyticAt (C.lift p.2)).comp
      (f := fun p : ℂ × PeriodOneHminusOne => C.lift p.2) ((C.lift_analytic p.2 hp.2).comp analyticAt_snd)
  have he : AnalyticAt ℂ (fun p : ℂ × PeriodOneHminusOne => p.1+C.energyShift) p :=
    analyticAt_fst.add analyticAt_const
  exact (analyticOnNhd_l2QuasiHillSolution_joint v _ (mem_univ _)).comp
    (f := fun p : ℂ × PeriodOneHminusOne => (p.1+C.energyShift,C.physicalProfile p.2)) (he.prod hu)

/-- The intrinsic discriminant is the trace of the two actual rough
quasi-derivative solution columns. All complex energies are included. -/
theorem hillHminusDiscriminant_eq_physicalSolution_trace (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (lambda : ℂ) :
    hillHminusDiscriminant q lambda =
      (C.physicalSolution q lambda (1,0) ⟨1,by constructor <;> norm_num⟩).1+
        (C.physicalSolution q lambda (0,1) ⟨1,by constructor <;> norm_num⟩).2 := by
  rw [hillHminusDiscriminant_eq_chart C q hq]
  exact hillMiuraL2Discriminant_eq_physicalQuasi (C.lift q) (lambda+C.energyShift)

/-- Different lift branches and different mass shifts give the same
actual physical monodromy trace on each chart overlap. -/
theorem physicalSolution_trace_eq_on_overlap (C D : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.domain) (hqD : q ∈ D.domain) (lambda : ℂ) :
    (C.physicalSolution q lambda (1,0) ⟨1,by constructor <;> norm_num⟩).1+
        (C.physicalSolution q lambda (0,1) ⟨1,by constructor <;> norm_num⟩).2 =
      (D.physicalSolution q lambda (1,0) ⟨1,by constructor <;> norm_num⟩).1+
        (D.physicalSolution q lambda (0,1) ⟨1,by constructor <;> norm_num⟩).2 :=
  (C.hillHminusDiscriminant_eq_physicalSolution_trace q hqC lambda).symm.trans
    (D.hillHminusDiscriminant_eq_physicalSolution_trace q hqD lambda)

end NLS.KdV.HillHminusMiuraChart
