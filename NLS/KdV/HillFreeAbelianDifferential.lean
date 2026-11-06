import NLS.KdV.HillFreeTerminalDifferential
import NLS.KdV.HillSignedAbelianAnalytic
/-! # The actual free Abelian coordinates have the normalized Fourier differential -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra
namespace NLS.KdV
variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillDirichletAbelianCoordinate_free_differential
    (n : ℕ) (hn : 1≤n) :
    ∃ Z : Coeff 2 → ℂ, AnalyticAt ℂ Z 0 ∧ Z 0=0 ∧
      (∀ h : Coeff 2, h∈Coeff.paritySubspace 0 → h 0=0 →
        (fderiv ℂ Z 0) h=(Real.sqrt (2*(n:ℝ)*Real.pi):ℂ)⁻¹*h (2*(n:ℤ))) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,hq,hr⟩ : RealPeriodOneHillPotential),
        Z (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn := by
  obtain ⟨T,hT,hT0,hDT,hTmatch⟩ := exists_hillDirichletAbelianTerminalFactor_free_differential hq hr n hn
  obtain ⟨F,hF,hFmatch⟩ := exists_hillSummedRegularAbelianCorrection_analytic_extension hq hr 0 hq hr n hn
  let K := hillLocalAbelianAmplitudePrefactor 0 hq hr n
  have hK : AnalyticAt ℂ K 0 := by
    simpa only [map_zero] using analyticAt_hillLocalAbelianAmplitudePrefactor 0 hq hr n hn
  have hFa : AnalyticAt ℂ F 0 := by simpa only [map_zero] using hF
  let M : Coeff 2 → ℂ := fun p => K p*exp (I*F p)
  have hM : AnalyticAt ℂ M 0 := hK.mul ((analyticAt_const.mul hFa).cexp)
  let Z : Coeff 2 → ℂ := fun p => T p*M p
  have hZ : AnalyticAt ℂ Z 0 := hT.mul hM
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,hq,hr⟩ : RealPeriodOneHillPotential),
      Z (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn := by
    filter_upwards [hTmatch,hFmatch,hillLocalAbelianAmplitudePrefactor_eventually_eq_physical 0 hq hr n hn] with p hpT hpF hpK
    dsimp only [Z,M,K]
    rw [hpT,hpF,hpK,hillDirichletAbelianCoordinate_eq_factor p.val p.property.1 p.property.2 n hn]
    ring
  have hK0 : K 0=(Real.sqrt (2*(n:ℝ)*Real.pi):ℂ)⁻¹ := by
    have he := (hillLocalAbelianAmplitudePrefactor_eventually_eq_physical 0 hq hr n hn).self_of_nhds
    simpa only [map_zero,hillAbelianAmplitudePrefactor_free hq hr n hn] using he
  have hF0 : F 0=0 := by
    simpa only [map_zero,hillSummedRegularAbelianCorrection_free hq hr n hn] using hFmatch.self_of_nhds
  have hM0 : M 0=(Real.sqrt (2*(n:ℝ)*Real.pi):ℂ)⁻¹ := by
    dsimp only [M]
    rw [hK0,hF0,mul_zero,exp_zero,mul_one]
  refine ⟨Z,hZ,by simp only [Z,hT0,zero_mul],?_,hmatch⟩
  intro h hh hm
  have hd := (hT.differentiableAt.hasFDerivAt.fun_mul hM.differentiableAt.hasFDerivAt).fderiv
  change fderiv ℂ Z 0=_ at hd
  rw [hd]
  change T 0*((fderiv ℂ M 0) h)+M 0*((fderiv ℂ T 0) h)=_
  rw [hT0,zero_mul,zero_add,hM0,hDT h hh hm]

theorem fderiv_hillDirichletAbelianCoordinate_free_of_eventuallyEq
    (n : ℕ) (hn : 1≤n) (C : Coeff 2 → ℂ) (hC : DifferentiableAt ℂ C 0)
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn)
    (h : Coeff 2) (hh : h∈Coeff.paritySubspace 0) (hm : h 0=0) :
    (fderiv ℂ C 0) h=(Real.sqrt (2*(n:ℝ)*Real.pi):ℂ)⁻¹*h (2*(n:ℤ)) := by
  obtain ⟨Z,hZ,_hZ0,hDZ,hZmatch⟩ := exists_hillDirichletAbelianCoordinate_free_differential hq hr n hn
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=Z (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch,hZmatch] with p hp hpZ
    exact hp.trans hpZ.symm
  have he := fderiv_eq_on_parity_of_eventuallyEq_realPotentials 0 hq hr C Z
    (by simpa only [map_zero] using hC) (by simpa only [map_zero] using hZ.differentiableAt) heq h hh
  simpa only [map_zero,hDZ h hh hm] using he

theorem exists_hillNegativeAbelianCoordinate_free_differential
    (n : ℕ) (hn : 1≤n) :
    ∃ H : Coeff 2 → ℂ, AnalyticAt ℂ H 0 ∧ H 0=0 ∧
      (∀ h : Coeff 2, h∈Coeff.paritySubspace 0 → h 0=0 →
        (fderiv ℂ H 0) h=(Real.sqrt (2*(n:ℝ)*Real.pi):ℂ)⁻¹*h (2*(-(n:ℤ)))) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,hq,hr⟩ : RealPeriodOneHillPotential),
        H (SpectralWeight.one.toCoeff p.val)=conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) := by
  obtain ⟨Z,hZ,hZ0,hDZ,hZmatch⟩ := exists_hillDirichletAbelianCoordinate_free_differential hq hr n hn
  let H : Coeff 2 → ℂ := fun p => conj (Z (star (Coeff.reflection p)))
  have hs := analyticAt_star_star hZ
  have hR : AnalyticAt ℂ (fun p : Coeff 2 => Coeff.reflection p) 0 :=
    Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _
  have hs0 : AnalyticAt ℂ (star ∘ Z ∘ star) (Coeff.reflection (0:Coeff 2)) := by
    simpa only [star_zero,map_zero] using hs
  have hH : AnalyticAt ℂ H 0 := by
    simpa only [H,Function.comp_def,Complex.star_def] using
      hs0.comp (f := fun p : Coeff 2 => Coeff.reflection p) hR
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,hq,hr⟩ : RealPeriodOneHillPotential),
      H (SpectralWeight.one.toCoeff p.val)=conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) := by
    filter_upwards [hZmatch] with p hp
    have he : star (Coeff.reflection (SpectralWeight.one.toCoeff p.val))=SpectralWeight.one.toCoeff p.val := by
      ext k
      change conj ((SpectralWeight.one.toCoeff p.val) (-k))=(SpectralWeight.one.toCoeff p.val) k
      rw [p.property.2 k,conj_conj]
    dsimp only [H]
    rw [he,hp]
  refine ⟨H,hH,by simp only [H,map_zero,star_zero,hZ0,map_zero],?_,hmatch⟩
  intro h hh hm
  have hpar : star (Coeff.reflection h)∈Coeff.paritySubspace 0 := by
    rw [Coeff.mem_paritySubspace]
    intro k hk
    have hz := (Coeff.mem_paritySubspace 0 h).mp hh (-k) (by omega)
    change conj (h (-k))=0
    rw [hz,map_zero]
  have hm0 : (star (Coeff.reflection h)) 0=0 := by
    change conj (h (-0))=0
    simp only [neg_zero,hm,map_zero]
  have hsd := hZ.differentiableAt.hasFDerivAt.star_star
  simp only [star_zero] at hsd
  have hRd : HasFDerivAt (fun p : Coeff 2 => Coeff.reflection p)
      Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap (0:Coeff 2) :=
    Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  have hd := hsd.comp (0:Coeff 2) hRd
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hd.fderiv
  change (fderiv ℂ H 0) h=conj ((fderiv ℂ Z 0) (star (Coeff.reflection h))) at he
  rw [hDZ _ hpar hm0,map_mul,map_inv₀,conj_ofReal] at he
  have hval : conj ((star (Coeff.reflection h)) (2*(n:ℤ)))=h (2*(-(n:ℤ))) := by
    change conj (conj (h (-(2*(n:ℤ)))))=h (2*(-(n:ℤ)))
    simp only [conj_conj,mul_neg]
  rw [hval] at he
  exact he
end NLS.KdV
