import NLS.ZakharovShabat.SourceCentralGapSpatialStationarity
import NLS.ZakharovShabat.SourceFiniteGapSobolevHamiltonian

/-! A genuine REAL Dirac source with only its central gap possibly open
is spatially constant. Actual finite-gap regularity and actual physical
momentum normalization prove this without an inverse spectral premise. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem source_nonzero_coefficients_eq_zero_of_noncentral_gaps_closed
    (φ : realTypeSourceSubmodule 2)
    (hclosed : ∀ n : ℤ, n ≠ 0 → canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n=0)
    (k : ℤ) (hk : k ≠ 0) : φ.val.fst k=0 ∧ φ.val.snd k=0 := by
  have hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
    apply (finite_singleton (0:ℤ)).subset
    intro n hn
    by_contra h
    exact hn (hclosed n h)
  let a := sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  have hi : sobolevSourceInclusion a=φ.val := sobolevSourceInclusion_sourceFiniteGapSobolevPair φ hf
  have ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a)) := hi.symm ▸ φ.property
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original (p := 2) (by simp) (by norm_num)
  have hd := Q.spatialDerivative_eq_zero_of_noncentral_gaps_closed a ha (by simpa only [hi] using hclosed)
  have hl := congrArg (fun ψ : CoeffPair 2 => ψ.fst k) hd
  have hr := congrArg (fun ψ : CoeffPair 2 => ψ.snd k) hd
  change (2:ℂ)*(I*(Real.pi:ℂ)*k*a.1.val k)=0 at hl
  change (2:ℂ)*(I*(Real.pi:ℂ)*k*a.2.val k)=0 at hr
  have hc : (2:ℂ)*I*(Real.pi:ℂ)*k ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (by exact_mod_cast hk)
  have hla : a.1.val k=0 := (mul_eq_zero.mp (by convert hl using 1; ring :
    ((2:ℂ)*I*(Real.pi:ℂ)*k)*a.1.val k=0)).resolve_left hc
  have hra : a.2.val k=0 := (mul_eq_zero.mp (by convert hr using 1; ring :
    ((2:ℂ)*I*(Real.pi:ℂ)*k)*a.2.val k=0)).resolve_left hc
  have hlf : a.1.val k=φ.val.fst k := by
    simpa only [sobolevSourceInclusion_fst,scalarInclusion_apply] using
      congrArg (fun ψ : CoeffPair 2 => ψ.fst k) hi
  have hrf : a.2.val k=φ.val.snd k := by
    simpa only [sobolevSourceInclusion_snd,scalarInclusion_apply] using
      congrArg (fun ψ : CoeffPair 2 => ψ.snd k) hi
  exact ⟨hlf.symm.trans hla,hrf.symm.trans hra⟩

/-- Full original source equality with its actual constant Fourier mode. -/
theorem source_eq_constant_of_noncentral_gaps_closed
    (φ : realTypeSourceSubmodule 2)
    (hclosed : ∀ n : ℤ, n ≠ 0 → canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n=0) :
    φ.val=WithLp.toLp 2 (lp.single 2 0 (φ.val.fst 0),lp.single 2 0 (φ.val.snd 0)) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext k
    change φ.val.fst k=(lp.single 2 0 (φ.val.fst 0) : Coeff 2) k
    by_cases hk : k=0
    · subst k; simp [lp.single_apply]
    · simpa only [lp.single_apply,Pi.single_apply,if_neg hk] using
        (source_nonzero_coefficients_eq_zero_of_noncentral_gaps_closed φ hclosed k hk).1
  · ext k
    change φ.val.snd k=(lp.single 2 0 (φ.val.snd 0) : Coeff 2) k
    by_cases hk : k=0
    · subst k; simp [lp.single_apply]
    · simpa only [lp.single_apply,Pi.single_apply,if_neg hk] using
        (source_nonzero_coefficients_eq_zero_of_noncentral_gaps_closed φ hclosed k hk).2

end NLS.ZakharovShabat
