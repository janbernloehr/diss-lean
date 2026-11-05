import NLS.KdV.HillMiuraCentralMean
import NLS.KdV.SingularDirichletMiuraEquation
import NLS.SequenceSpaces.PeriodOneMiuraCompactDerivative
import NLS.SequenceSpaces.WeakFirstOrderRegularity

/-! A weak kernel of the actual L2-to-Hminus Miura linearization gives
an actual zero-frequency periodic Dirac eigenvector. The full H1 domain
is recovered by the verified weak first-order regularity theorem. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem zero_mem_diagonalSpectrum_of_weakFirstOrder (u h : Coeff 2) (hne : h ≠ 0)
    (he : ∀ k : ℤ, 2*I*(Real.pi:ℂ)*k*h k+(∑' j : ℤ, u (k-j)*h j)=0) :
    (0:ℂ) ∈ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u)) := by
  let v : Coeff 2 := (-1/2:ℂ) • u
  have hv : ∀ k : ℤ, I*(Real.pi:ℂ)*k*h k=(∑' j : ℤ, v (k-j)*h j)+(0 : Coeff 2) k := by
    intro k
    simp only [v,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_zero,Pi.zero_apply,add_zero]
    have ht : (∑' j : ℤ, ((-1/2:ℂ)*u (k-j))*h j)=
        (-1/2:ℂ)*(∑' j : ℤ, u (k-j)*h j) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      ring
    rw [ht]
    linear_combination (1/2:ℂ)*he k
  let a := weakFirstOrderLift v h 0 hv
  let b := Coeff.periodDoubleSobolev a
  have hD : derivative a=(-1/2:ℂ) • potentialMul (by simp) u a := by
    ext k
    change I*(Real.pi:ℂ)*k*h k=(-1/2:ℂ)*(potentialMul (by simp) u a k)
    rw [potentialMul_apply]
    change I*(Real.pi:ℂ)*k*h k=(-1/2:ℂ)*(∑' j : ℤ, u (k-j)*h j)
    linear_combination (1/2:ℂ)*he k
  have hbD : derivative b= -potentialMul (by simp) (Coeff.periodDouble u) b := by
    rw [Coeff.derivative_periodDoubleSobolev,hD,map_smul,potentialMul_periodDoubleSobolev]
    simp only [map_smul,smul_smul]
    norm_num
  have hbne : b ≠ 0 := by
    intro hb
    apply hne
    ext k
    have hh := congrArg (fun c : ScalarDomain 2 => c.val (2*k)) hb
    change Coeff.periodDouble (scalarInclusion a) (2*k)=0 at hh
    rw [Coeff.periodDouble_even,scalarInclusion_weakFirstOrderLift] at hh
    exact hh
  apply (mem_periodicSpectrum_iff_exists_eigenvector (by simp) _ 0).mpr
  refine ⟨(b,I • b),?_,?_⟩
  · intro heq
    exact hbne (congrArg Prod.fst heq)
  · rw [zero_smul,periodOnePotential_apply,hillMiuraDiagonal_fst,hillMiuraDiagonal_snd]
    change (I • derivative b+potentialMul (by simp) (Coeff.periodDouble u) (I • b),
      -I • derivative (I • b)+potentialMul (by simp) (Coeff.periodDouble u) b)=(0,0)
    simp only [map_smul,smul_smul,I_mul_I,neg_mul,neg_neg,one_smul,hbD,smul_neg,
      neg_add_cancel]

theorem periodOneMiuraLinearization_injective_of_real_mean_ne_zero
    (u : PeriodOneRealL2) (hu : u.val 0 ≠ 0) :
    Function.Injective (periodOneMiuraLinearization u.val) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro h hh
  by_contra hn
  have he (k : ℤ) : 2*I*(Real.pi:ℂ)*k*h k+
      (∑' j : ℤ, ((2:ℂ) • u.val) (k-j)*h j)=0 := by
    have hk := congrArg (fun p : PeriodOneHminusOne => p.val k) hh
    rw [periodOneMiuraLinearization_apply] at hk
    simp only [WeightedCoeff.zero_val] at hk
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    have ht : (∑' j : ℤ, ((2:ℂ)*u.val (k-j))*h j)=
        2*(∑' j : ℤ, u.val (k-j)*h j) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      ring
    rw [ht]
    exact hk
  have hz := zero_mem_diagonalSpectrum_of_weakFirstOrder ((2:ℂ) • u.val) h hn he
  let w : PeriodOneRealL2 := ⟨(2:ℂ) • u.val,by
    intro k
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,u.property,map_mul,map_ofNat]⟩
  have hzero := (hillMiura_zero_mem_spectrum_iff_mean_zero w).mp hz
  change (2:ℂ)*u.val 0=0 at hzero
  exact hu ((mul_eq_zero.mp hzero).resolve_left (by norm_num))

end NLS.KdV
