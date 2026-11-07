import NLS.KdV.HillProductFixedPeriods
import NLS.ZakharovShabat.SourceCanonicalRootJointAnalytic

/-! Literal Hill product periods jointly in independent l2 zero data,
energy shift and the ACTUAL complex Dirac source. The open domain is
exactly the moving-gap complement of the canonical root. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillEnergyProductJointIntegrand (n : ℕ+)
    (t : ℂ × (lp (fun _ : ℕ+ => ℂ) 2 × (ℂ × CoeffPair 2))) : ℂ :=
  (2*t.1*hillEnergySequenceProduct n (t.1^2-t.2.2.1,t.2.1))/
    sourceCanonicalRoot (by norm_num) (by norm_num) t.2.2.2 t.1

def hillEnergyProductJointDomain (W : Set (CoeffPair 2)) :
    Set (ℂ × (lp (fun _ : ℕ+ => ℂ) 2 × (ℂ × CoeffPair 2))) :=
  {t | (t.1,t.2.2.2) ∈ sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W}

theorem isOpen_hillEnergyProductJointDomain (W : Set (CoeffPair 2))
    (hW : IsOpen (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W)) :
    IsOpen (hillEnergyProductJointDomain W) :=
  hW.preimage (continuous_fst.prodMk continuous_snd.snd.snd)

theorem analyticOnNhd_hillEnergyProductJointIntegrand (W : Set (CoeffPair 2))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct (by norm_num) (by norm_num))
      (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W)) (n : ℕ+) :
    AnalyticOnNhd ℂ (hillEnergyProductJointIntegrand n) (hillEnergyProductJointDomain W) := by
  intro t ht
  have hE : AnalyticAt ℂ
      (fun s : ℂ × (lp (fun _ : ℕ+ => ℂ) 2 × (ℂ × CoeffPair 2)) =>
        (s.1^2-s.2.2.1,s.2.1)) t :=
    ((analyticAt_fst.pow 2).sub (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd))).prod
      (analyticAt_fst.comp analyticAt_snd)
  have hP := (analyticAt_hillEnergySequenceProduct n _).comp hE
  have hR : AnalyticAt ℂ
      (fun s : ℂ × (lp (fun _ : ℕ+ => ℂ) 2 × (ℂ × CoeffPair 2)) =>
        sourceCanonicalRoot (by norm_num) (by norm_num) s.2.2.2 s.1) t :=
    (hroot (t.1,t.2.2.2) ht).comp
      (f := fun s : ℂ × (lp (fun _ : ℕ+ => ℂ) 2 × (ℂ × CoeffPair 2)) => (s.1,s.2.2.2))
      (analyticAt_fst.prod (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)))
  exact ((analyticAt_const.mul analyticAt_fst).mul hP).div hR
    (sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) t.2.2.2 t.1 ht.2)

def hillEnergyProductJointPeriod (n : ℕ+) (a : ℂ) (R : ℝ)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × (ℂ × CoeffPair 2)) : ℂ :=
  (2*Real.pi:ℂ)⁻¹*(∮ z in C(a,R),hillEnergyProductJointIntegrand n (z,t))

theorem hillEnergyProductJointPeriod_eq_fixed (n : ℕ+) (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergyProductJointPeriod n (D.center:ℂ) D.radius (d,(c,ψ)) =
      hillEnergyProductFixedPeriod n c ψ D d := rfl

theorem analyticOnNhd_hillEnergyProductJointPeriod (W V : Set (CoeffPair 2))
    (hD : IsOpen (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct (by norm_num) (by norm_num))
      (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W))
    (hV : IsOpen V) (hVW : V ⊆ W) (a : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : ∀ ψ ∈ V, sphere a R ⊆ sourceCanonicalRootDomain (by norm_num) (by norm_num) ψ)
    (n : ℕ+) : AnalyticOnNhd ℂ (hillEnergyProductJointPeriod n a R) (univ ×ˢ (univ ×ˢ V)) := by
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic (hillEnergyProductJointIntegrand n)
    (isOpen_hillEnergyProductJointDomain W hD)
    (analyticOnNhd_hillEnergyProductJointIntegrand W hroot n) a R hR
    (isOpen_univ.prod (isOpen_univ.prod hV)) (by
      intro t ht z hz
      exact ⟨hVW ht.2.2,hcircle t.2.2 ht.2.2 hz⟩)
  intro t ht
  exact analyticAt_const.mul (hi t ht)

end NLS.KdV
