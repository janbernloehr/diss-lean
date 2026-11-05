import NLS.KdV.HillHminusPsiCharts
import NLS.KdV.MiuraRealSource
import NLS.ZakharovShabat.SourcePsiContourConjugation
import NLS.ComplexAnalysis.DenseSegmentComplement

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- The actual entire energy numerator has the original real symmetry,
including its analytically filled zero-frequency value. -/
theorem MiuraHillPsiFamily.numerator_conj_of_real (A : MiuraHillPsiFamily)
    (u : PeriodOneRealL2) (n : ℕ+) (E : ℂ) :
    A.numerator n (conj E,u.val)=conj (A.numerator n (E,u.val)) := by
  let a : Coeff 2 := A.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u.val)
  have hroots (k : ℤ) : (displacedRoots a k).im=0 := by
    change (displacedRoots (A.roots ((n:ℕ):ℤ) (hillMiuraRealSource u).val : Coeff 2) k).im=0
    rw [A.verified.real_agreement ((n:ℕ):ℤ) (hillMiuraRealSource u)]
    have hr := sourcePsiGapRoot_mem_realDeletedCoeffSubmodule (by norm_num) (by norm_num)
      ((n:ℕ):ℤ) (hillMiuraRealSource u) k
    simpa only [displacedRoots,Complex.add_im,Complex.mul_im,Complex.ofReal_im,
      Complex.intCast_im,mul_zero,zero_mul,zero_add] using hr
  have hψ (z : ℂ) := sourcePsiCandidate_conj_of_real_roots (by norm_num) (by norm_num)
    ((n:ℕ):ℤ) a hroots z
  have hnz (E : ℂ) (hE : E≠0) :
      A.numerator n (conj E,u.val)=conj (A.numerator n (E,u.val)) := by
    let z := Complex.sqrt E
    have hzsq : z^2=E := complex_sqrt_sq _
    have hz : z≠0 := by intro h; rw [h,zero_pow (by norm_num : (2:ℕ)≠0)] at hzsq; exact hE hzsq.symm
    have hodd : sourcePsiCandidate ((n:ℕ):ℤ) (conj z,a)-
        sourcePsiCandidate ((n:ℕ):ℤ) (-conj z,a)=
        conj (sourcePsiCandidate ((n:ℕ):ℤ) (z,a)-sourcePsiCandidate ((n:ℕ):ℤ) (-z,a)) := by
      rw [←map_neg,hψ z,hψ (-z),map_sub]
    have hh := (A.numerator_frequency_identity n u.val (conj z)).trans
      (hodd.trans (congrArg conj (A.numerator_frequency_identity n u.val z)).symm)
    simp only [map_mul,map_ofNat] at hh
    have hc : conj z≠0 := by
      intro h
      apply hz
      simpa only [conj_conj,map_zero] using congrArg conj h
    have he := mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ)≠0) hc) hh
    simpa only [←map_pow,hzsq] using he
  have hF : Continuous (fun E : ℂ => A.numerator n (E,u.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro E
    exact ((A.analytic_numerator n (E,u.val) ⟨mem_univ _,A.real_mem_source u⟩).comp
      (f := fun z : ℂ => (z,u.val)) (analyticAt_id.prod analyticAt_const)).continuousAt
  exact continuous_eqOn_of_dense_on_open ({0}:Set ℂ)ᶜ univ (dense_compl_singleton 0) isOpen_univ
    (fun E => A.numerator n (conj E,u.val)) (fun E => conj (A.numerator n (E,u.val)))
    (hF.comp continuous_conj).continuousOn (continuous_conj.comp hF).continuousOn
    (by intro E hE; exact hnz E (by simpa using hE.2)) (mem_univ E)

/-- Every real-form source of an actual chart gives real energy
numerators with its fixed real energy translation. -/
theorem HillHminusPsiChart.numerator_conj_of_real (P : HillHminusPsiChart)
    (q : PeriodOneHminusOne)
    (hreal : ∀ k : ℤ, P.miura.lift q (-k)=conj (P.miura.lift q k))
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)) (n : ℕ+) (E : ℂ) :
    P.numerator n (conj E,q)=conj (P.numerator n (E,q)) := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift q,hreal⟩
  have he : conj (E+P.miura.energyShift)=conj E+P.miura.energyShift := by rw [map_add,hshift,conj_ofReal]
  change P.family.numerator n (conj E+P.miura.energyShift,u.val)=
    conj (P.family.numerator n (E+P.miura.energyShift,u.val))
  rw [←he]
  exact P.family.numerator_conj_of_real u n _

theorem HillHminusPsiChart.numerator_real_of_real (P : HillHminusPsiChart)
    (q : PeriodOneHminusOne)
    (hreal : ∀ k : ℤ, P.miura.lift q (-k)=conj (P.miura.lift q k))
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)) (n : ℕ+) (x : ℝ) :
    (P.numerator n ((x:ℂ),q)).im=0 := by
  have h := P.numerator_conj_of_real q hreal c hshift n (x:ℂ)
  rw [conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

end NLS.KdV
