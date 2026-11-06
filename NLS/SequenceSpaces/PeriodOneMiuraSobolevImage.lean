import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.SobolevAbsoluteSummability
import NLS.SequenceSpaces.SpectralConvolution
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Sobolev regularity of the literal distributional Miura image

Weighted convolution and the exact unit-period derivative transfer all
nonnegative Sobolev orders from an L2 lift to its original rough image.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS

private theorem weight_ext (a b : Weight) (h : a.value=b.value) : a=b := by
  cases a
  cases b
  cases h
  rfl

theorem periodOneMiura_image_mem_sobolev_of_all
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c))
    (hu : ∀ t : ℝ, 0≤t → Memℓp (fun n => (Weight.sobolev t n : ℂ)*u n) 2)
    (s : ℝ) (hs : 0≤s) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2 := by
  let w := SpectralWeight.sobolev s hs
  have hw : w.toWeight=Weight.sobolev s := by
    exact weight_ext _ _ (funext (SpectralWeight.sobolev_apply s hs))
  let a : WeightedCoeff w.toWeight 2 := ⟨u,by rw [hw]; exact hu s hs⟩
  let b : WeightedCoeff w.toWeight 1 := ⟨u,by
    rw [hw]
    exact WeightedCoeff.memlp_sobolev_one_of_two_succ s (hu (s+1) (by linarith))⟩
  let a' : WeightedCoeff (Weight.sobolev (s+1)) 2 := ⟨u,hu (s+1) (by linarith)⟩
  let d := WeightedCoeff.sobolevDerivative s a'
  let D : WeightedCoeff w.toWeight 2 := ⟨d.val,by rw [hw];exact d.property⟩
  let Q : WeightedCoeff w.toWeight 2 :=
    (2 : ℂ) • D+w.convolution a b-
      WeightedCoeff.ofFinsupp w.toWeight 2 (Finsupp.single 0 c)
  have heq : Q.val=q.val := by
    funext n
    have he := congrArg (fun p : PeriodOneHminusOne => p.val n) himage
    change (periodOneMiura u).val n=q.val n+(periodOneL2Inclusion (lp.single 2 0 c)).val n at he
    rw [periodOneMiura_apply,periodOneL2Inclusion_apply] at he
    change 2*(WeightedCoeff.sobolevDerivative s a').val n+(w.convolution a b).val n-
      (WeightedCoeff.ofFinsupp w.toWeight 2 (Finsupp.single 0 c)).val n=q.val n
    rw [WeightedCoeff.sobolevDerivative_apply,SpectralWeight.convolution_apply,
      WeightedCoeff.ofFinsupp_apply]
    dsimp only [a,a',b]
    simp only [lp.single_apply,Pi.single_apply,Finsupp.single_apply,show 0=n ↔ n=0 from eq_comm] at he ⊢
    linear_combination he
  rw [← heq,← hw]
  exact Q.property

end NLS
