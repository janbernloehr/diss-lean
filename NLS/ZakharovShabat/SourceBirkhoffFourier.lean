import NLS.ZakharovShabat.SourceBirkhoffFreeDifferential
import NLS.ZakharovShabat.SourceBirkhoffJacobian

/-! # The free Birkhoff Jacobian is the Fourier transform

The bounded transform includes the reflection of the first signed
source component. Equality is proved for every finite exponent above
one, using restriction below two and density above two.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The linear Fourier transform in the source's signed component convention. -/
def sourceBirkhoffFourier : CoeffPair p →L[ℂ] (Coeff p × Coeff p) :=
  let a := Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp (CoeffPair.toMax p).toContinuousLinearMap)
  let b := (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp (CoeffPair.toMax p).toContinuousLinearMap
  (((-1 : ℂ)/(Real.sqrt 2 : ℂ)) • (a+b)).prod
    (((1 : ℂ)/((Real.sqrt 2 : ℂ)*I)) • (a-b))

@[simp] theorem sourceBirkhoffFourier_fst (h : CoeffPair p) (n : ℤ) :
    (sourceBirkhoffFourier h).1 n = -(h.fst (-n)+h.snd n)/(Real.sqrt 2 : ℂ) := by
  change (((-1 : ℂ)/(Real.sqrt 2 : ℂ)) • (Coeff.reflection h.fst + h.snd)) n = _
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_add, Pi.add_apply, Coeff.reflection_apply]
  ring

@[simp] theorem sourceBirkhoffFourier_snd (h : CoeffPair p) (n : ℤ) :
    (sourceBirkhoffFourier h).2 n = (h.fst (-n)-h.snd n)/((Real.sqrt 2 : ℂ)*I) := by
  change (((1 : ℂ)/((Real.sqrt 2 : ℂ)*I)) • (Coeff.reflection h.fst - h.snd)) n = _
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_sub, Pi.sub_apply, Coeff.reflection_apply]
  ring

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The full free rectangular cotangents at every finite exponent above one. -/
theorem birkhoffXY_fderiv_zero
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (hrW : realTypeSourceLocus p ⊆ W) (n : ℤ) (h : CoeffPair p) :
    (fderiv ℂ (sourceBirkhoffX hp hp1 n s) 0) h = (sourceBirkhoffFourier h).1 n ∧
    (fderiv ℂ (sourceBirkhoffY hp hp1 n s) 0) h = (sourceBirkhoffFourier h).2 n := by
  obtain ⟨V₀,C,V,_,_,_,_,_,_,t,E⟩ := exists_sourceAngularTheta_theorem13_1_iv
    (p := 2) (by simp) (by norm_num)
  have he (k : CoeffPair 2) := E.toSourceAngularEtaLocalCommonDomainData.birkhoffXY_fderiv_zero_hilbert
    V E.source_open E.source_subset (E.real_subset (show IsRealType (CoeffPair.toMax 2 0) from by simp)) n k
  by_cases hp2 : p ≤ 2
  · have hd := D.fderiv_birkhoffXY_exponent E.toSourceAngularEtaLocalCommonDomainData
      W V hW E.source_open hWB E.source_subset hrW E.real_subset hp2 n ⟨0,by simp⟩
    simpa using And.intro
      ((congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hd.1).trans (he (CoeffPair.exponentInclusion hp2 h)).1)
      ((congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hd.2).trans (he (CoeffPair.exponentInclusion hp2 h)).2)
  · have h2p : (2 : ℝ≥0∞) ≤ p := le_of_not_ge hp2
    have hd := E.toSourceAngularEtaLocalCommonDomainData.fderiv_birkhoffXY_exponent D
      V W E.source_open hW E.source_subset hWB E.real_subset hrW h2p n ⟨0,by simp⟩
    let f (k : CoeffPair p) := ((fderiv ℂ (sourceBirkhoffX hp hp1 n s) 0) k,
      (fderiv ℂ (sourceBirkhoffY hp hp1 n s) 0) k)
    let g (k : CoeffPair p) := ((sourceBirkhoffFourier k).1 n, (sourceBirkhoffFourier k).2 n)
    have hf : Continuous f := (fderiv ℂ (sourceBirkhoffX hp hp1 n s) 0).continuous.prodMk
      (fderiv ℂ (sourceBirkhoffY hp hp1 n s) 0).continuous
    have hg : Continuous g :=
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp (sourceBirkhoffFourier (p := p)).continuous.fst).prodMk
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp (sourceBirkhoffFourier (p := p)).continuous.snd)
    have hfg : f = g := CoeffPair.eq_of_continuous_of_finsupp hp f g hf hg (by
      intro a
      have hx := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L (CoeffPair.ofFinsupp a)) hd.1
      have hy := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L (CoeffPair.ofFinsupp a)) hd.2
      have hv := he (CoeffPair.ofFinsupp a)
      apply Prod.ext
      · simpa [f,g] using hx.symm.trans hv.1
      · simpa [f,g] using hy.symm.trans hv.2)
    exact Prod.mk.inj (congrFun hfg h)

end SourceAngularEtaLocalCommonDomainData

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Equality of bounded operators: the actual Birkhoff Jacobian at zero
is exactly the explicitly normalized Fourier transform. -/
theorem jacobian_zero
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    sourceBirkhoffJacobian hp hp1 s 0 = sourceBirkhoffFourier := by
  ext h : 1
  apply Prod.ext <;> ext n
  · exact (D.jacobian_coordinates 0 (D.real_subset (show IsRealType (CoeffPair.toMax p 0) from by simp)) h n).1.trans
      (D.angular.birkhoffXY_fderiv_zero W D.source_open D.source_subset D.real_subset n h).1
  · exact (D.jacobian_coordinates 0 (D.real_subset (show IsRealType (CoeffPair.toMax p 0) from by simp)) h n).2.trans
      (D.angular.birkhoffXY_fderiv_zero W D.source_open D.source_subset D.real_subset n h).2

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
