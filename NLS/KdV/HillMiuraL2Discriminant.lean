import NLS.MKdV.MiuraL2HillDiscriminant
import NLS.MKdV.PeriodOneMiuraSourceComparison
import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.KdV.HillL2ConstantShift

/-! # The L2 Miura trace and its exact physical L2-image comparison

The original diagonal NLS discriminant is even in frequency, by the
physical H1 Miura identity and H1 density in L2. Entire even descent
therefore gives a jointly analytic energy trace on all complex L2
Miura inputs. Whenever the distributional Miura image is L2, the
checked regularity theorem identifies it with the actual Hill trace.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.MKdV
open scoped ENNReal
namespace NLS.KdV

def hillMiuraDiagonal : Coeff 2 →L[ℂ] CoeffPair 2 := CoeffPair.inlCLM+CoeffPair.inrCLM

@[simp] theorem hillMiuraDiagonal_fst (a : Coeff 2) : (hillMiuraDiagonal a).fst = a := by
  change a+0 = a
  simp

@[simp] theorem hillMiuraDiagonal_snd (a : Coeff 2) : (hillMiuraDiagonal a).snd = a := by
  change 0+a = a
  simp

theorem hillMiuraDiagonal_scalarInclusion (a : ScalarDomain 2) :
    hillMiuraDiagonal (scalarInclusion a) = sobolevSourceInclusion (a,a) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext k
    change (hillMiuraDiagonal (scalarInclusion a)).fst k = (sobolevSourceInclusion (a,a)).fst k
    rw [hillMiuraDiagonal_fst,sobolevSourceInclusion_fst,scalarInclusion_apply]
  · ext k
    change (hillMiuraDiagonal (scalarInclusion a)).snd k = (sobolevSourceInclusion (a,a)).snd k
    rw [hillMiuraDiagonal_snd,sobolevSourceInclusion_snd,scalarInclusion_apply]

def hillMiuraFrequencyTrace (u : Coeff 2) (z : ℂ) : ℂ :=
  canonicalDiscriminant (by simp) (periodOnePotential (hillMiuraDiagonal u)) z

theorem analyticOnNhd_hillMiuraFrequencyTrace_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillMiuraFrequencyTrace p.2 p.1) univ := by
  intro p _
  have hd : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillMiuraDiagonal t.2) p :=
    (hillMiuraDiagonal.analyticAt p.2).comp analyticAt_snd
  exact (analyticOnNhd_canonicalDiscriminant_periodOne (by simp) (by norm_num)
    (p.1,hillMiuraDiagonal p.2) (mem_univ _)).comp
      (f := fun t : ℂ × Coeff 2 => (t.1,hillMiuraDiagonal t.2)) (analyticAt_fst.prod hd)

theorem hillMiuraFrequencyTrace_scalarInclusion (a : ScalarDomain 2) (z : ℂ) :
    hillMiuraFrequencyTrace (scalarInclusion a) z =
      hillL2Discriminant (sobolevMiuraHillPotential a) (z^2) := by
  rw [hillMiuraFrequencyTrace,hillMiuraDiagonal_scalarInclusion,hillL2Discriminant_miura]
  simpa only [miuraDiagonalSource_periodOneMiuraCurve] using
    canonicalDiscriminant_miuraDiagonalSource (periodOneMiuraCurve a) z

theorem hillMiuraFrequencyTrace_even (u : Coeff 2) (z : ℂ) :
    hillMiuraFrequencyTrace u (-z) = hillMiuraFrequencyTrace u z := by
  have hc (w : ℂ) : Continuous (fun a : Coeff 2 => hillMiuraFrequencyTrace a w) := by
    have h : Continuous (fun p : ℂ × Coeff 2 => hillMiuraFrequencyTrace p.2 p.1) :=
      analyticOnNhd_hillMiuraFrequencyTrace_joint.continuous
    have hm : Continuous (fun a : Coeff 2 => (w,a)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using h.comp hm
  have he := (scalarInclusion_denseRange (p := 2) (by simp)).equalizer (hc (-z)) (hc z) (by
    funext a
    change hillMiuraFrequencyTrace (scalarInclusion a) (-z) = hillMiuraFrequencyTrace (scalarInclusion a) z
    rw [hillMiuraFrequencyTrace_scalarInclusion,neg_sq,hillMiuraFrequencyTrace_scalarInclusion])
  exact congrFun he u

def hillMiuraL2Discriminant (u : Coeff 2) (lambda : ℂ) : ℂ :=
  hillMiuraFrequencyTrace u (Complex.sqrt lambda)

theorem analyticOnNhd_hillMiuraL2Discriminant_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillMiuraL2Discriminant p.2 p.1) univ :=
  ComplexAnalysis.analyticOnNhd_entire_even_square_descent
    (fun p : ℂ × Coeff 2 => hillMiuraFrequencyTrace p.2 p.1)
    analyticOnNhd_hillMiuraFrequencyTrace_joint hillMiuraFrequencyTrace_even
    Complex.sqrt ComplexAnalysis.complex_sqrt_sq

theorem hillMiuraL2Discriminant_scalarInclusion (a : ScalarDomain 2) (lambda : ℂ) :
    hillMiuraL2Discriminant (scalarInclusion a) lambda =
      hillL2Discriminant (sobolevMiuraHillPotential a) lambda := by
  rw [hillMiuraL2Discriminant,hillMiuraFrequencyTrace_scalarInclusion,ComplexAnalysis.complex_sqrt_sq]

/-- An L2 distributional Miura image has the actual physical Hill trace. -/
theorem hillMiuraL2Discriminant_eq_hillL2 (u q : Coeff 2)
    (himage : periodOneMiura u = periodOneL2Inclusion q) (lambda : ℂ) :
    hillMiuraL2Discriminant u lambda = hillL2Discriminant (Coeff.periodDouble q) lambda := by
  let a : ScalarDomain 2 := ⟨u,periodOneMiura_memlp_sobolev_one u q himage⟩
  have ha : scalarInclusion a = u := by ext k; exact scalarInclusion_apply a k
  have hq : sobolevMiuraUnitPotential a = q := by
    ext k
    have h := congrArg (fun p : PeriodOneHminusOne => p.val k) himage
    rw [periodOneMiura_apply,periodOneL2Inclusion_apply] at h
    rw [sobolevMiuraUnitPotential_apply]
    exact h
  rw [← ha,hillMiuraL2Discriminant_scalarInclusion,sobolevMiuraHillPotential,hq]

theorem periodDouble_single_zero (c : ℂ) :
    Coeff.periodDouble (lp.single 2 0 c) = lp.single 2 0 c := by
  ext k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he,Coeff.periodDouble_even]
    simp [lp.single_apply,Pi.single_apply]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,Coeff.periodDouble_odd]
    have hn : 2*(k/2)+1 ≠ 0 := by omega
    simp [lp.single_apply,hn]

/-- The exact energy translation for a Miura chart whose image differs by a constant. -/
theorem hillMiuraL2Discriminant_eq_hillL2_of_shifted_image (u q : Coeff 2) (c lambda : ℂ)
    (himage : periodOneMiura u = periodOneL2Inclusion (q+lp.single 2 0 c)) :
    hillMiuraL2Discriminant u (lambda+c) = hillL2Discriminant (Coeff.periodDouble q) lambda := by
  rw [hillMiuraL2Discriminant_eq_hillL2 u _ himage,map_add,periodDouble_single_zero,
    hillL2Discriminant_add_const]

end NLS.KdV
