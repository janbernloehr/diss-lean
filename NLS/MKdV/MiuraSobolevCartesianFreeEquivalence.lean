import NLS.MKdV.MiuraSobolevPositiveCartesian
import NLS.ComplexAnalysis.LinearEquivMeanTransport

/-! # Actual free Cartesian Banach isomorphisms on every native H^s

Even Sobolev source weights commute with the signed Fourier pairs.
The target weight factorization transports the already explicit free
L² inverse to every native positive Hilbert target of order s+1/2.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.MKdV

def miuraPositiveSobolevWeightEquiv (s : ℕ) : MiuraPositiveSobolevTarget s ≃L[ℂ] MiuraPositiveCartesianTarget :=
  ((WeightedCoeff.positiveWeightEquiv (miuraCartesianWeight s) (Weight.sobolev (1/2)) 2).prodCongr
    (WeightedCoeff.positiveWeightEquiv (miuraCartesianWeight s) (Weight.sobolev (1/2)) 2)).prodCongr
      (ContinuousLinearEquiv.refl ℂ ℂ)

def miuraSobolevCartesianFreeEquiv (s : ℕ) : ScalarSobolev s ≃L[ℂ] MiuraPositiveSobolevTarget s :=
  ((WeightedCoeff.weightIsometry (Weight.sobolev (s : ℝ)) 2).toContinuousLinearEquiv.trans
    miuraCartesianFreeEquiv).trans (miuraPositiveSobolevWeightEquiv s).symm

theorem miuraSobolevCartesianFreeJacobian_signed (s : ℕ) (n : ℤ) (hn : 0 < n) (h : ScalarSobolev s) :
    miuraSobolevPositiveEval s n (miuraSobolevCartesianFreeJacobian s h) =
      (sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2)*(-(h.val (-n)+h.val n)/(Real.sqrt 2 : ℂ)),
       -(sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2)*((h.val (-n)-h.val n)/((Real.sqrt 2 : ℂ)*I)))) := by
  have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
  have hnat : 1 ≤ n.toNat := by omega
  have he := miuraSobolevCartesianFreeJacobian_positive s n.toNat hnat h
  rw [hi] at he
  exact he

theorem miuraSobolevCartesianFreeEquiv_positive (s : ℕ) (n : ℤ) (hn : 0 < n) (h : ScalarSobolev s) :
    miuraSobolevPositiveEval s n (miuraSobolevCartesianFreeEquiv s h) =
      miuraSobolevPositiveEval s n (miuraSobolevCartesianFreeJacobian s h) := by
  let h0 := WeightedCoeff.weightIsometry (Weight.sobolev (s : ℝ)) 2 h
  have hh0 (k : ℤ) : h0 k = (Weight.sobolev (s : ℝ) k : ℂ)*h.val k := rfl
  have hL := miuraCartesianFreeJacobian_signed n hn h0
  have hS := miuraSobolevCartesianFreeJacobian_signed s n hn h
  have hxL := congrArg Prod.fst hL
  have hyL := congrArg Prod.snd hL
  have hxS := congrArg Prod.fst hS
  have hyS := congrArg Prod.snd hS
  change (miuraCartesianFreeJacobian h0).1.1.val.val n = _ at hxL
  change (miuraCartesianFreeJacobian h0).1.2.val.val n = _ at hyL
  change (miuraSobolevCartesianFreeJacobian s h).1.1.val.val n = _ at hxS
  change (miuraSobolevCartesianFreeJacobian s h).1.2.val.val n = _ at hyS
  have hw : Weight.sobolev (s : ℝ) (-n) = Weight.sobolev (s : ℝ) n := by simp [Weight.sobolev_apply]
  have hden : (miuraCartesianWeight s n : ℂ) ≠ 0 := (miuraCartesianWeight s).complex_ne_zero n
  apply Prod.ext
  · change ((Weight.sobolev (1/2) n : ℂ)*(miuraCartesianFreeJacobian h0).1.1.val.val n)/
        (miuraCartesianWeight s n : ℂ) = (miuraSobolevCartesianFreeJacobian s h).1.1.val.val n
    rw [hxL,hxS,hh0,hh0,hw]
    apply (div_eq_iff hden).mpr
    rw [miuraCartesianWeight_factor]
    push_cast
    ring
  · change ((Weight.sobolev (1/2) n : ℂ)*(miuraCartesianFreeJacobian h0).1.2.val.val n)/
        (miuraCartesianWeight s n : ℂ) = (miuraSobolevCartesianFreeJacobian s h).1.2.val.val n
    rw [hyL,hyS,hh0,hh0,hw]
    apply (div_eq_iff hden).mpr
    rw [miuraCartesianWeight_factor]
    push_cast
    ring

theorem miuraCartesianFreeEquiv_mean (h : Coeff 2) : (miuraCartesianFreeEquiv h).2 = h 0 :=
  miuraCartesianFreeJacobian_mean h

theorem miuraSobolevWeight_zero (s : ℕ) (h : ScalarSobolev s) :
    WeightedCoeff.weightIsometry (Weight.sobolev (s : ℝ)) 2 h 0 = h.val 0 := by
  change (Weight.sobolev (s : ℝ) 0 : ℂ)*h.val 0 = h.val 0
  simp [Weight.sobolev_apply]

theorem miuraSobolevCartesianFreeEquiv_mean (s : ℕ) (h : ScalarSobolev s) :
    (miuraSobolevCartesianFreeEquiv s h).2 = h.val 0 := by
  have he := NLS.ComplexAnalysis.trans_prodCongr_refl_symm_snd
    (WeightedCoeff.weightIsometry (Weight.sobolev (s : ℝ)) 2).toContinuousLinearEquiv miuraCartesianFreeEquiv
    ((WeightedCoeff.positiveWeightEquiv (miuraCartesianWeight s) (Weight.sobolev (1/2)) 2).prodCongr
      (WeightedCoeff.positiveWeightEquiv (miuraCartesianWeight s) (Weight.sobolev (1/2)) 2)) h
  exact he.trans ((miuraCartesianFreeEquiv_mean _).trans (miuraSobolevWeight_zero s h))

theorem miuraPositiveSobolevTarget_ext (s : ℕ) (a b : MiuraPositiveSobolevTarget s)
    (hp : ∀ n : ℤ, 0 < n → miuraSobolevPositiveEval s n a = miuraSobolevPositiveEval s n b)
    (hm : a.2 = b.2) : a = b := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      funext n
      by_cases hn : 0 < n
      · exact congrArg Prod.fst (hp n hn)
      · exact (a.1.1.property n (by omega)).trans (b.1.1.property n (by omega)).symm
    · apply Subtype.ext
      apply Subtype.ext
      funext n
      by_cases hn : 0 < n
      · exact congrArg Prod.snd (hp n hn)
      · exact (a.1.2.property n (by omega)).trans (b.1.2.property n (by omega)).symm
  · exact hm

/-- Equality of bounded operators: the actual native free derivative is
an explicit equivalence, at every integer s>=0. -/
theorem miuraSobolevCartesianFreeJacobian_eq_equiv (s : ℕ) :
    miuraSobolevCartesianFreeJacobian s = (miuraSobolevCartesianFreeEquiv s).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro h
  apply miuraPositiveSobolevTarget_ext s
  · intro n hn
    exact (miuraSobolevCartesianFreeEquiv_positive s n hn h).symm
  · exact (miuraSobolevCartesianFreeJacobian_mean s h).trans (miuraSobolevCartesianFreeEquiv_mean s h).symm

end NLS.MKdV
