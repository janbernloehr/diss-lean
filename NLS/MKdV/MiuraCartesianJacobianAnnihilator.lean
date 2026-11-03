import NLS.MKdV.MiuraCartesianAnnihilatorOffMode

/-! # The full native Cartesian Jacobian has no nonzero annihilator

The modal cancellations are summed in the actual half-order target norm.
No assertion about cross-mode zero brackets is used.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraCartesian_annihilator_own_value (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (P : (ℂ × ℂ) →L[ℂ] ℂ) (L : MiuraPositiveCartesianTarget →L[ℂ] ℂ)
    (hL : L.comp (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) = 0) :
    L (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
      (l2GardnerDirection (miuraCartesianObservable m P) (scalarInclusion a))) =
      L (miuraCartesianInsert m (miuraPositiveCartesianEval m
        (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
          (l2GardnerDirection (miuraCartesianObservable m P) (scalarInclusion a))))) := by
  apply WeightedCoeff.cotangent_value_of_modes_except (Weight.sobolev (1/2)) 2 (by simp) L
    _ (miuraCartesianJacobian_Gardner_observable_mean a ha m hm P) m (by omega)
  intro k hk hkm
  have hi : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.le
  have hn : 1 ≤ k.toNat := by omega
  have hmn : m ≠ k.toNat := by omega
  have h := miuraCartesian_annihilator_off_mode a ha m k.toNat hm hn hmn P L hL
  change L (WeightedCoeff.positiveCartesianInsert (Weight.sobolev (1/2)) 2 (k.toNat : ℤ)
    (miuraPositiveCartesianEval k.toNat (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
      (l2GardnerDirection (miuraCartesianObservable m P) (scalarInclusion a))))) = 0 at h
  rw [hi] at h
  exact h

theorem miuraCartesian_annihilator_all_modal_coefficients (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (L : MiuraPositiveCartesianTarget →L[ℂ] ℂ)
    (hL : L.comp (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) = 0) :
    miuraCartesianCotangentX L m = 0 ∧ miuraCartesianCotangentY L m = 0 := by
  have hown := miuraCartesianJacobian_own_Gardner_pairs a ha m hm
  have hx := miuraCartesian_annihilator_own_value a ha m hm (ContinuousLinearMap.fst ℂ ℂ ℂ) L hL
  have hy := miuraCartesian_annihilator_own_value a ha m hm (ContinuousLinearMap.snd ℂ ℂ ℂ) L hL
  have hzx := congrArg (fun Q : Coeff 2 →L[ℂ] ℂ => Q
    (l2GardnerDirection (miuraCartesianX m) (scalarInclusion a))) hL
  have hzy := congrArg (fun Q : Coeff 2 →L[ℂ] ℂ => Q
    (l2GardnerDirection (miuraCartesianY m) (scalarInclusion a))) hL
  change L (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
    (l2GardnerDirection (miuraCartesianX m) (scalarInclusion a))) = 0 at hzx
  change L (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
    (l2GardnerDirection (miuraCartesianY m) (scalarInclusion a))) = 0 at hzy
  change L (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
    (l2GardnerDirection (miuraCartesianX m) (scalarInclusion a))) =
      L (miuraCartesianInsert m (miuraPositiveCartesianEval m (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
        (l2GardnerDirection (miuraCartesianX m) (scalarInclusion a))))) at hx
  change L (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
    (l2GardnerDirection (miuraCartesianY m) (scalarInclusion a))) =
      L (miuraCartesianInsert m (miuraPositiveCartesianEval m (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
        (l2GardnerDirection (miuraCartesianY m) (scalarInclusion a))))) at hy
  rw [hzx,hown.1,miuraCartesianCotangent_insert L m hm] at hx
  rw [hzy,hown.2,miuraCartesianCotangent_insert L m hm] at hy
  exact ⟨by simpa using hy.symm,by simpa using hx.symm⟩

theorem miuraCartesianJacobian_annihilator_eq_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (L : MiuraPositiveCartesianTarget →L[ℂ] ℂ)
    (hL : L.comp (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) = 0) : L = 0 := by
  have hmodal (n : ℤ) (hn : 0 < n) :
      L (WeightedCoeff.positiveCartesianInsert (Weight.sobolev (1/2)) 2 n (1,0)) = 0 ∧
      L (WeightedCoeff.positiveCartesianInsert (Weight.sobolev (1/2)) 2 n (0,1)) = 0 := by
    have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
    have h := miuraCartesian_annihilator_all_modal_coefficients a ha n.toNat (by omega) L hL
    change L (WeightedCoeff.positiveCartesianInsert (Weight.sobolev (1/2)) 2 (n.toNat : ℤ) (1,0)) = 0 ∧
      L (WeightedCoeff.positiveCartesianInsert (Weight.sobolev (1/2)) 2 (n.toNat : ℤ) (0,1)) = 0 at h
    rwa [hi] at h
  have hmean := WeightedCoeff.cotangent_eq_mean_of_modal_zero (Weight.sobolev (1/2)) 2 (by simp) L hmodal
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  have hz := congrArg (fun Q : Coeff 2 →L[ℂ] ℂ => Q (lp.single 2 0 1)) hL
  change L (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a) (lp.single 2 0 1)) = 0 at hz
  have ht := hmean (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a) (lp.single 2 0 1))
  rw [hz,miuraCartesianJacobian_mean _ har] at ht
  simp only [lp.single_apply,Pi.single_eq_same,one_mul] at ht
  apply ContinuousLinearMap.ext
  intro z
  rw [hmean z,← ht,mul_zero]
  rfl

end NLS.MKdV
