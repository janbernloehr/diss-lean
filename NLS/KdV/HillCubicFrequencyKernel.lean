import NLS.KdV.HillLocalDiagonalResolvent

/-! # Actual cubic frequency kernel versus the Dirichlet velocity polynomial -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

private theorem norm_cubic_dirichlet_kernel_error_le (z F G q₀ : ℂ) (CF CG : ℝ)
    (hz : 1≤‖z‖) (hCF : 0≤CF)
    (hphase : ‖z‖^3*‖F+I*z‖≤CF)
    (hlocal : ‖z‖^4*‖G-I/(2*z)-I*q₀/(4*z^3)‖≤CG) :
    ‖z‖*‖F^3*G+z^2/2+q₀/4‖≤
      (1+CF)^3*CG+CF*((1+CF)^2+(1+CF)+1)*(1+‖q₀‖) := by
  let r := ‖z‖
  let B := 1+CF
  let A := -I*z
  let L := I/(2*z)+I*q₀/(4*z^3)
  have hr : 1≤r := hz
  have hrpos : 0<r := by linarith
  have hz0 : z≠0 := norm_pos_iff.mp hrpos
  have hδ : ‖F+I*z‖≤CF := by
    have hr3 : 1≤r^3 := one_le_pow₀ hr
    nlinarith [mul_le_mul_of_nonneg_right hr3 (norm_nonneg (F+I*z))]
  have hFnorm : ‖F‖≤B*r := by
    have he : F=(-I*z)+(F+I*z) := by ring
    have hn := norm_add_le (-I*z) (F+I*z)
    rw [← he] at hn
    simp only [norm_mul,norm_neg,norm_I,one_mul] at hn
    dsimp only [B,r]
    nlinarith
  have hAnorm : ‖A‖=r := by dsimp only [A,r];simp
  have hcube : ‖F^3-A^3‖≤CF*(B^2+B+1) := by
    have he : F^3-A^3=(F+I*z)*(F^2+F*A+A^2) := by dsimp only [A];ring
    have hsum : ‖F^2+F*A+A^2‖≤r^2*(B^2+B+1) := by
      have hn := (norm_add_le (F^2+F*A) (A^2)).trans
        (add_le_add (norm_add_le (F^2) (F*A)) le_rfl)
      simp only [norm_pow,norm_mul,hAnorm] at hn
      have hp := pow_le_pow_left₀ (norm_nonneg F) hFnorm 2
      have hm := mul_le_mul_of_nonneg_right hFnorm hrpos.le
      nlinarith
    have hδ2 : r^2*‖F+I*z‖≤CF := by
      have hh : r^2≤r^3 := by nlinarith [sq_nonneg r]
      exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans hphase
    rw [he,norm_mul]
    calc
      _ ≤ ‖F+I*z‖*(r^2*(B^2+B+1)) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      _ = (r^2*‖F+I*z‖)*(B^2+B+1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hδ2 (by dsimp only [B];positivity)
  have hL : r*‖L‖≤1+‖q₀‖ := by
    have he : L=(I/2)/z+(I*q₀/4)/z^3 := by dsimp only [L];ring
    have h1 := norm_weighted_laurent_term_le z (I/2) hz 1 1 le_rfl
    have h2 := norm_weighted_laurent_term_le z (I*q₀/4) hz 1 3 (by omega)
    simp only [pow_one] at h1 h2
    have hn := mul_le_mul_of_nonneg_left (norm_add_le ((I/2)/z) ((I*q₀/4)/z^3)) (norm_nonneg z)
    rw [← he,mul_add] at hn
    have hIa : ‖(I/2:ℂ)‖=1/2 := by simp
    have hIb : ‖I*q₀/4‖=‖q₀‖/4 := by simp
    rw [hIa] at h1
    rw [hIb] at h2
    nlinarith [norm_nonneg q₀]
  have hmodel : A^3*L=-z^2/2-q₀/4 := by
    dsimp only [A,L]
    field_simp [hz0]
    ring_nf
    simp only [I_pow_four]
    ring
  have he : F^3*G+z^2/2+q₀/4=F^3*(G-L)+(F^3-A^3)*L := by linear_combination hmodel
  have hG : r^4*‖G-L‖≤CG := by simpa only [L,sub_add_eq_sub_sub] using hlocal
  rw [he]
  have h1 : r*‖F^3*(G-L)‖≤B^3*CG := by
    rw [norm_mul,norm_pow]
    calc
      _ ≤ r*((B*r)^3*‖G-L‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg F) hFnorm 3) (norm_nonneg _)) hrpos.le
      _ = B^3*(r^4*‖G-L‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hG (by dsimp only [B];positivity)
  have h2 : r*‖(F^3-A^3)*L‖≤CF*(B^2+B+1)*(1+‖q₀‖) := by
    rw [norm_mul]
    calc
      _ = ‖F^3-A^3‖*(r*‖L‖) := by ring
      _ ≤ _ := mul_le_mul hcube hL (by positivity) (by dsimp only [B];positivity)
  have hh := mul_le_mul_of_nonneg_left (norm_add_le (F^3*(G-L)) ((F^3-A^3)*L)) hrpos.le
  rw [mul_add r] at hh
  exact hh.trans (add_le_add h1 h2)

theorem exists_hillL2RealCutPrimitive_upper_arc_cubic_decay
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0) :
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n → ∀ t : Icc (0:ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      (hillFreeBandFrequency n)^3*
        ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)+I*z‖≤C := by
  let f : ℝ → ℂ := fun x => Q (x : AddCircle (2:ℝ))
  let a := I*classicalQuadraticInvariant f/4
  let b := I*classicalHamiltonian f/16
  obtain ⟨D,hD,K₀,hbound⟩ := exists_hillL2RealCutPrimitive_upper_arc_physical_error_bound Q hq hr hf hp hmean 0
  obtain ⟨K₁,hK₁⟩ := Filter.eventually_atTop.mp (tendsto_hillFreeBandFrequency.eventually_ge_atTop 1)
  refine ⟨D+‖a‖+‖b‖+1,by positivity,max K₀ K₁,?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let r := hillFreeBandFrequency n
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  have hz : ‖z‖=r := norm_hillFreeUpperFrequency n t
  have hr1 : 1≤r := hK₁ n ((le_max_right _ _).trans hn)
  have hrpos : 0<r := by linarith
  have hz0 : z≠0 := norm_pos_iff.mp (by rw [hz];exact hrpos)
  have h := hbound n ((le_max_left _ _).trans hn) t
  simp only [Finset.range_zero,Finset.sum_empty,sub_zero,Nat.zero_add] at h
  have he : F+I*(z-classicalQuadraticInvariant f/(4*z^3)-classicalHamiltonian f/(16*z^5))=
      F+I*z-a/z^3-b/z^5 := by dsimp only [a,b];ring
  change ‖F+I*(z-classicalQuadraticInvariant f/(4*z^3)-classicalHamiltonian f/(16*z^5))‖≤D/(2*r)^5 at h
  rw [he] at h
  have hcross : ‖F+I*z-a/z^3-b/z^5‖*(2*r)^5≤D := (le_div_iff₀ (by positivity)).mp h
  have hrpow : r^3≤(2*r)^5 := (pow_le_pow_left₀ hrpos.le (by linarith : r≤2*r) 3).trans
    (pow_le_pow_right₀ (by linarith : 1≤2*r) (by omega : 3≤5))
  have hδ : r^3*‖F+I*z-a/z^3-b/z^5‖≤D := by
    nlinarith [mul_le_mul_of_nonneg_left hrpow (norm_nonneg (F+I*z-a/z^3-b/z^5))]
  have ha := norm_weighted_laurent_term_le z a (by rw [hz];exact hr1) 3 3 le_rfl
  have hb := norm_weighted_laurent_term_le z b (by rw [hz];exact hr1) 3 5 (by omega)
  rw [hz] at ha hb
  have hsum : F+I*z=(F+I*z-a/z^3-b/z^5)+a/z^3+b/z^5 := by ring
  have hn1 := norm_add_le ((F+I*z-a/z^3-b/z^5)+a/z^3) (b/z^5)
  have hn2 := norm_add_le (F+I*z-a/z^3-b/z^5) (a/z^3)
  have hnorm := hn1.trans (add_le_add hn2 le_rfl)
  rw [← hsum] at hnorm
  have hh := mul_le_mul_of_nonneg_left hnorm (pow_nonneg hrpos.le 3)
  rw [mul_add (r^3),mul_add (r^3)] at hh
  change r^3*‖F+I*z‖≤_
  linarith

theorem exists_hillL2CubicDirichletKernel_upper_arc_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0) :
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n → ∀ t : Icc (0:ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      (hillFreeBandFrequency n)*
        ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)^3*
          (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)/
            hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2))+
              z^2/2+Q (0 : AddCircle (2:ℝ))/4‖≤C := by
  obtain ⟨CF,hCF,KF,hphase⟩ := exists_hillL2RealCutPrimitive_upper_arc_cubic_decay Q hq hr hf hp hmean
  obtain ⟨CG,hCG,KG,hlocal⟩ := exists_hillL2Dirichlet_div_root_local_cubic_error_bound Q hq hr hf hp
  obtain ⟨K₁,hK₁⟩ := Filter.eventually_atTop.mp (tendsto_hillFreeBandFrequency.eventually_ge_atTop 1)
  let C := (1+CF)^3*CG+CF*((1+CF)^2+(1+CF)+1)*(1+‖Q (0 : AddCircle (2:ℝ))‖)
  refine ⟨C+1,by dsimp only [C];positivity,max (max KF KG) K₁,?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  have hz : ‖z‖=hillFreeBandFrequency n := norm_hillFreeUpperFrequency n t
  have hr1 := hK₁ n ((le_max_right _ _).trans hn)
  have hF := hphase n ((le_max_left _ _).trans ((le_max_left _ _).trans hn)) t
  have hG := hlocal n ((le_max_right _ _).trans ((le_max_left _ _).trans hn)) t
  have hh := norm_cubic_dirichlet_kernel_error_le z
    (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2))
    (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)/
      hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2))
    (Q (0 : AddCircle (2:ℝ))) CF CG (by rw [hz];exact hr1) hCF.le
    (by simpa only [hz] using hF) (by simpa only [hz] using hG)
  rw [hz] at hh
  exact hh.trans (by dsimp only [C];linarith)

end NLS.KdV
