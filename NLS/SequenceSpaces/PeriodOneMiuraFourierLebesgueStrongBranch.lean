import NLS.ComplexAnalysis.AnalyticQuadraticResolvent
import NLS.SequenceSpaces.PeriodOneMiuraStrongCharts
import NLS.SequenceSpaces.PeriodOneFractionalMiuraProduct
import NLS.SequenceSpaces.PeriodOneFourierLebesgueMassResolvent
import NLS.SequenceSpaces.PeriodOneMiuraFourierLebesgueEquivalence
import NLS.SequenceSpaces.ExponentEmbedding

/-! # Analytic Fourier-Lebesgue restrictions of the same rough Miura branch

A Sobolev inverse germ gives a quadratic term in a stronger Hilbert norm.
The literal mass resolvent then realizes that SAME inverse germ analytically
in the native Fourier-Lebesgue norm, including the endpoint s=-1/2.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

/-- The identity on raw coefficients into the common rough source. -/
def periodOneFourierLebesgueImageInclusion (s p : ℝ) (hs : -1/2≤s) (hp : 2<p)
    [Fact (1≤ENNReal.ofReal p)] :
    WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) →L[ℂ] PeriodOneHminusOne :=
  (WeightedCoeff.sobolevInclusion (by
    have hδ : 0<1/(2*p) := by positivity
    linarith : -1≤s-1/2+1/(2*p))).comp (WeightedCoeff.fourierLebesgueHilbertInclusion s p hp)

@[simp] theorem periodOneFourierLebesgueImageInclusion_apply
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (a : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)) (n : ℤ) :
    (periodOneFourierLebesgueImageInclusion s p hs hp a).val n=a.val n := by
  simp only [periodOneFourierLebesgueImageInclusion,ContinuousLinearMap.comp_apply,
    WeightedCoeff.sobolevInclusion_apply,WeightedCoeff.fourierLebesgueHilbertInclusion_apply]

/-- Every Sobolev restriction of a fixed rough inverse yields its actual
native Fourier-Lebesgue analytic restriction. -/
theorem exists_analytic_fourierLebesgue_periodOneMiura_branch
    (m : ℕ) (U : Set PeriodOneHminusOne) (G : PeriodOneHminusOne → Coeff 2)
    (hstrong : ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
      periodOneSobolevImageInclusion t ht q∈U →
      ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
        ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2,
          AnalyticOnNhd ℂ g V ∧ ∀ x∈V,
            periodOneSobolevImageInclusion t ht x∈U ∧
            WeightedCoeff.sobolevToL2 ht (g x)=G (periodOneSobolevImageInclusion t ht x) ∧
            periodOneSobolevShiftedMiura m t ht (g x)=x)
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (q : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p))
    (hq : periodOneFourierLebesgueImageInclusion s p hs hp q∈U) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)), IsOpen V ∧ q∈V ∧
      ∃ g : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) →
        WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p),
        AnalyticOnNhd ℂ g V ∧ ∀ x∈V,
          periodOneFourierLebesgueImageInclusion s p hs hp x∈U ∧
          ∀ n : ℤ, (g x).val n=G (periodOneFourierLebesgueImageInclusion s p hs hp x) n := by
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
  let B := periodOneFractionalMiuraProductCLM t ht d hd
  apply NLS.ComplexAnalysis.quadratic_resolvent_properties_preimage L J
    (periodOneFourierLebesgueMassInverse m s (ENNReal.ofReal p)) B g W hW hga q hqW
    (fun x y => periodOneFourierLebesgueImageInclusion s p hs hp x∈U ∧
      ∀ n : ℤ, y.val n=G (periodOneFourierLebesgueImageInclusion s p hs hp x) n)
  intro x hx
  obtain ⟨hU,hagree,hsolve⟩ := hg (L x) hx
  rw [hJL] at hU hagree
  refine ⟨hU,?_⟩
  intro n
  have he := congrArg (fun a => a.val n) hsolve
  simp only [periodOneSobolevShiftedMiura_apply,hL] at he
  have hcoeff : (periodOneFourierLebesgueMassInverse m s (ENNReal.ofReal p)
      (x-J (B (g (L x)) (g (L x))))).val n=(g (L x)).val n := by
    rw [periodOneFourierLebesgueMassInverse_apply,WeightedCoeff.sub_val,hJ]
    dsimp only [B]
    rw [periodOneFractionalMiuraProductCLM_apply,periodOneFractionalMiuraProduct_apply]
    rw [←he]
    simp only [add_sub_cancel_right,inv_mul_cancel_left₀ (periodOneMassSymbol_ne_zero m n)]
  rw [hcoeff]
  exact (WeightedCoeff.sobolevToL2_apply ht (g (L x)) n).symm.trans
    (congrArg (fun a : Coeff 2 => a n) hagree)

end NLS
