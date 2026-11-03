import NLS.KdV.HillDirichletReality

/-! # Wronskian, trace and real-energy reality of the actual rough scalar Hill flow. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate ENNReal
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2FrequencyStateCurve_wronskian (q : Coeff 2) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    (hillL2FrequencyStateCurve q z (1,0) t).1*(hillL2FrequencyStateCurve q z (0,1) t).2-
      (hillL2FrequencyStateCurve q z (0,1) t).1*(hillL2FrequencyStateCurve q z (1,0) t).2=1 := by
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  have hA := congrArg (fun Y : Curve (ℂ × ℂ) => Y t)
    (l2SolutionCurve_linearCombination u z (constantUpperInitialVector z (1,0)))
  have hB := congrArg (fun Y : Curve (ℂ × ℂ) => Y t)
    (l2SolutionCurve_linearCombination u z (constantUpperInitialVector z (0,1)))
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply] at hA hB
  have hd : (l2SolutionCurve u z (1,0) t).1*(l2SolutionCurve u z (0,1) t).2-
      (l2SolutionCurve u z (0,1) t).1*(l2SolutionCurve u z (1,0) t).2=1 := by
    simpa [l2FundamentalMatrix,Matrix.det_fin_two] using det_l2FundamentalMatrix u z t
  simp only [hillL2FrequencyStateCurve_apply]
  change (constantUpperStateMap z (l2SolutionCurve u z (constantUpperInitialVector z (1,0)) t)).1*
    (constantUpperStateMap z (l2SolutionCurve u z (constantUpperInitialVector z (0,1)) t)).2-
    (constantUpperStateMap z (l2SolutionCurve u z (constantUpperInitialVector z (0,1)) t)).1*
    (constantUpperStateMap z (l2SolutionCurve u z (constantUpperInitialVector z (1,0)) t)).2=1
  rw [hA,hB]
  simp only [constantUpperStateMap_apply,constantUpperInitialVector,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,mul_one,sub_zero,zero_sub,one_mul]
  calc
    _ = (l2SolutionCurve u z (1,0) t).1*(l2SolutionCurve u z (0,1) t).2-
      (l2SolutionCurve u z (0,1) t).1*(l2SolutionCurve u z (1,0) t).2 := by
        ring_nf
        simp only [I_sq]
        ring
    _ = 1 := hd

theorem hillL2FrequencyStateCurve_real (q : Coeff 2) (hq : IsRealHillPotential q) (z : ℂ)
    (hz : (z^2).im=0) (v : ℂ × ℂ) (hv : v.1.im=0 ∧ v.2.im=0) (t : Icc (0 : ℝ) 1) :
    (hillL2FrequencyStateCurve q z v t).1.im=0 ∧ (hillL2FrequencyStateCurve q z v t).2.im=0 := by
  let S : Coeff 2 → Coeff 2 := fun a => (1/2 : ℂ) • (a+star (Coeff.reflection a))
  have hS : Continuous S := (continuous_id.add (Coeff.reflection.continuous.star)).const_smul (1/2 : ℂ)
  let F : Coeff 2 → ℂ × ℂ := fun a => hillL2FrequencyStateCurve a z v t
  have hc : Continuous F := (continuous_eval_const t).comp (continuous_hillL2FrequencyStateCurve z v)
  have hfinite (a : ℤ →₀ ℂ) : F (S (Coeff.ofFinsupp a))=
      (conj (F (S (Coeff.ofFinsupp a))).1,conj (F (S (Coeff.ofFinsupp a))).2) := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    let R : C(AddCircle (2 : ℝ),ℂ) := (1/2 : ℂ) • (Q+star Q)
    have hQ : Fourier.continuousFourierCLM Q=Coeff.ofFinsupp (p := 2) a := by
      ext k
      rw [Fourier.continuousFourierCLM_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    have hcoeff (T : C(AddCircle (2 : ℝ),ℂ)) :
        SpectralWeight.one.toCoeff (hillContinuousCoefficients T)=Fourier.continuousFourierCLM T := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,Fourier.continuousFourierCLM_apply]
    have hR : SpectralWeight.one.toCoeff (hillContinuousCoefficients R)=S (Coeff.ofFinsupp a) := by
      rw [hcoeff]
      dsimp only [R,S]
      rw [map_smul,map_add,Fourier.continuousFourierCLM_star,hQ]
    have hr : ∀ s, (hillUnitPotentialCurve R s).im=0 := by
      intro s
      simp [R,hillUnitPotentialCurve,Complex.mul_im]
    dsimp only [F]
    rw [← hR,hillL2FrequencyStateCurve_eq_classical]
    have hh := classicalHillFlow_conj (hillUnitPotentialCurve R) hr (z^2) v t
    rwa [Complex.conj_eq_iff_im.mpr hz,Complex.conj_eq_iff_im.mpr hv.1,Complex.conj_eq_iff_im.mpr hv.2] at hh
  have he : (fun a : Coeff 2 => F (S a))=(fun a : Coeff 2 => (conj (F (S a)).1,conj (F (S a)).2)) :=
    (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer (hc.comp hS)
      (((hc.comp hS).fst.star).prodMk ((hc.comp hS).snd.star)) (funext hfinite)
  have hfix : S q=q := by
    ext k
    simp only [S,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_add,Pi.add_apply,
      lp.star_apply,Coeff.reflection_apply,hq k,starRingEnd_apply,star_star]
    ring
  have hh := congrFun he q
  rw [hfix] at hh
  exact ⟨Complex.conj_eq_iff_im.mp (congrArg Prod.fst hh).symm,
    Complex.conj_eq_iff_im.mp (congrArg Prod.snd hh).symm⟩

theorem hillL2FrequencyStateCurve_trace (q : Coeff 2) (z : ℂ) :
    (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1+
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2=hillL2FrequencyDiscriminant q z := by
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  have hA := congrArg (fun Y : Curve (ℂ × ℂ) => Y t)
    (l2SolutionCurve_linearCombination u z (constantUpperInitialVector z (1,0)))
  have hB := congrArg (fun Y : Curve (ℂ × ℂ) => Y t)
    (l2SolutionCurve_linearCombination u z (constantUpperInitialVector z (0,1)))
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply] at hA hB
  have ht : hillL2FrequencyDiscriminant q z=(l2SolutionCurve u z (1,0) t).1+(l2SolutionCurve u z (0,1) t).2 := by
    simp [hillL2FrequencyDiscriminant,l2Discriminant,l2Monodromy,l2FundamentalMatrix,Matrix.trace,Fin.sum_univ_two,t,u]
    rfl
  rw [ht]
  change (constantUpperStateMap z (l2SolutionCurve u z (constantUpperInitialVector z (1,0)) t)).1+
      (constantUpperStateMap z (l2SolutionCurve u z (constantUpperInitialVector z (0,1)) t)).2=_
  rw [hA,hB]
  simp only [constantUpperStateMap_apply,constantUpperInitialVector,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,mul_one,sub_zero,zero_sub,one_mul]
  ring_nf
  simp only [I_sq]
  ring


end NLS.KdV
