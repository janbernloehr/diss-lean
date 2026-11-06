import NLS.ComplexAnalysis.AnalyticAffineQuadraticResolvent
import NLS.KdV.HillHminusRetainedMiuraEtaChart
import NLS.SequenceSpaces.PeriodOneMiuraFourierLebesgueStrongBranch

/-! # Native Fourier-Lebesgue germs of ANY retained actual Miura chart

The chart is not replaced. Its retained native Sobolev germs and the
literal unshifted Miura equation realize the SAME lift analytically in
FL^(s+1,p), including s=-1/2 and every finite real p>2.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

theorem exists_fourierLebesgue_native_Miura_lift (P : HillHminusPsiChart)
    (hstrong : HasAllNativeMiuraGerms P)
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (q : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p))
    (hq : periodOneFourierLebesgueImageInclusion s p hs hp q∈P.miura.domain) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)), IsOpen V ∧ q∈V ∧
      ∃ g : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) →
        WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p),
        AnalyticOnNhd ℂ g V ∧ ∀ x∈V,
          periodOneFourierLebesgueImageInclusion s p hs hp x∈P.miura.domain ∧
          ∀ n : ℤ, (g x).val n=P.miura.lift (periodOneFourierLebesgueImageInclusion s p hs hp x) n := by
  let t : ℝ := s+1/2+1/(2*p)
  let d : ℝ := 1/2+1/(2*p)
  have hδ : 0<1/(2*p) := by positivity
  have ht : 0≤t := by dsimp only [t];linarith
  have hd : 1/2<d := by dsimp only [d];linarith
  let L : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) →L[ℂ]
      WeightedCoeff (Weight.sobolev (t-1)) 2 :=
    (WeightedCoeff.sobolevInclusion (by dsimp only [t];linarith : t-1≤s-1/2+1/(2*p))).comp
      (WeightedCoeff.fourierLebesgueHilbertInclusion s p hp)
  have hL (x : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)) (n : ℤ) :
      (L x).val n=x.val n := by
    simp only [L,ContinuousLinearMap.comp_apply,WeightedCoeff.sobolevInclusion_apply,
      WeightedCoeff.fourierLebesgueHilbertInclusion_apply]
  have hJL (x : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)) :
      periodOneSobolevImageInclusion t ht (L x)=periodOneFourierLebesgueImageInclusion s p hs hp x := by
    apply Subtype.ext
    funext n
    simp only [periodOneSobolevImageInclusion_apply,hL,periodOneFourierLebesgueImageInclusion_apply]
  obtain ⟨W,hW,hqW,g,hga,hg⟩ := hstrong t ht (L q) (by rw [hJL];exact hq)
  have h2p : (2 : ℝ≥0∞)≤ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp.le
  let J : WeightedCoeff (Weight.sobolev (t-d)) 2 →L[ℂ]
      WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) :=
    (WeightedCoeff.exponentInclusion (Weight.sobolev s) h2p).comp
      (WeightedCoeff.sobolevInclusion (by dsimp only [t,d];linarith : s≤t-d))
  have hJ (a : WeightedCoeff (Weight.sobolev (t-d)) 2) (n : ℤ) : (J a).val n=a.val n := by
    simp only [J,ContinuousLinearMap.comp_apply,WeightedCoeff.exponentInclusion_apply,
      WeightedCoeff.sobolevInclusion_apply]
  let K : WeightedCoeff (Weight.sobolev t) 2 →L[ℂ]
      WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) :=
    (WeightedCoeff.exponentInclusion (Weight.sobolev s) h2p).comp
      (WeightedCoeff.sobolevInclusion (by dsimp only [t];linarith : s≤t))
  have hK (a : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) : (K a).val n=a.val n := by
    simp only [K,ContinuousLinearMap.comp_apply,WeightedCoeff.exponentInclusion_apply,
      WeightedCoeff.sobolevInclusion_apply]
  let B := periodOneFractionalMiuraProductCLM t ht d hd
  let k : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) :=
    WeightedCoeff.ofFinsupp _ _ (Finsupp.single 0 P.miura.energyShift)
  have hk (n : ℤ) : k.val n=(lp.single 2 0 P.miura.energyShift : Coeff 2) n := by
    simp only [k,WeightedCoeff.ofFinsupp_apply,lp.single_apply,Pi.single_apply,
      Finsupp.single_apply,show 0=n ↔ n=0 from eq_comm]
  apply NLS.ComplexAnalysis.affine_quadratic_resolvent_properties_preimage L J K
    (periodOneFourierLebesgueMassInverse 0 s (ENNReal.ofReal p)) B k g W hW hga q hqW
    (fun x y => periodOneFourierLebesgueImageInclusion s p hs hp x∈P.miura.domain ∧
      ∀ n : ℤ, y.val n=P.miura.lift (periodOneFourierLebesgueImageInclusion s p hs hp x) n)
  intro x hx
  obtain ⟨hU,hagree⟩ := hg (L x) hx
  rw [hJL] at hU hagree
  refine ⟨hU,?_⟩
  intro n
  have himage := P.miura.image _ hU
  rw [←hagree] at himage
  have he := congrArg (fun a : PeriodOneHminusOne => a.val n) himage
  simp only [periodOneMiura_apply,WeightedCoeff.add_val,periodOneL2Inclusion_apply,
    WeightedCoeff.sobolevToL2_apply,periodOneFourierLebesgueImageInclusion_apply] at he
  have hcoeff : (periodOneFourierLebesgueMassInverse 0 s (ENNReal.ofReal p)
      (x+k-J (B (g (L x)) (g (L x)))+K (g (L x)))).val n=(g (L x)).val n := by
    rw [periodOneFourierLebesgueMassInverse_apply,WeightedCoeff.add_val,WeightedCoeff.sub_val,
      WeightedCoeff.add_val,hk,hJ,hK]
    dsimp only [B]
    rw [periodOneFractionalMiuraProductCLM_apply,periodOneFractionalMiuraProduct_apply]
    have hlinear : x.val n+(lp.single 2 0 P.miura.energyShift : Coeff 2) n-
        (∑' j : ℤ, (g (L x)).val (n-j)*(g (L x)).val j)+(g (L x)).val n=
        periodOneMassSymbol 0 n*(g (L x)).val n := by
      simp only [periodOneMassSymbol,Nat.cast_zero,zero_add,Complex.ofReal_one]
      linear_combination he.symm
    rw [hlinear,inv_mul_cancel_left₀ (periodOneMassSymbol_ne_zero 0 n)]
  rw [hcoeff]
  exact (WeightedCoeff.sobolevToL2_apply ht (g (L x)) n).symm.trans
    (congrArg (fun a : Coeff 2 => a n) hagree)

end NLS.KdV.HillHminusPsiChart
