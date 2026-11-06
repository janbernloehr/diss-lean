import NLS.KdV.HillHilbertRootCoordinates

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



def hillAbelianRootUpdate (m : ℕ) (t : Coeff 2 × ℂ) : Coeff 2 :=
  Coeff.deleteCoordinate (m:ℤ) t.1 + lp.single 2 (m:ℤ) ((t.2-(freeHillValue m:ℂ))/(m:ℂ))

theorem hillAbelianRootUpdate_apply_same (m : ℕ) (a : Coeff 2) (s : ℂ) :
    hillAbelianRootUpdate m (a,s) (m:ℤ) = (s-(freeHillValue m:ℂ))/(m:ℂ) := by
  simp only [hillAbelianRootUpdate,lp.coeFn_add,Pi.add_apply,Coeff.deleteCoordinate_apply_same,
    lp.single_apply,Pi.single_eq_same,zero_add]

theorem hillAbelianRootUpdate_apply_other (m : ℕ) (a : Coeff 2) (s : ℂ) (j : ℤ) (hj : j ≠ m) :
    hillAbelianRootUpdate m (a,s) j = a j := by
  simp only [hillAbelianRootUpdate,lp.coeFn_add,Pi.add_apply,
    Coeff.deleteCoordinate_apply_other _ _ hj,lp.single_apply_ne _ _ _ hj,add_zero]

theorem analyticOnNhd_hillAbelianRootUpdate (m : ℕ) : AnalyticOnNhd ℂ (hillAbelianRootUpdate m) univ := by
  intro t _
  have hd := (Coeff.deleteCoordinate (p := 2) (m:ℤ)).analyticAt t.1
  have hs := (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 (m:ℤ)).analyticAt
    ((t.2-(freeHillValue m:ℂ))/(m:ℂ))
  exact (hd.comp (f := fun t : Coeff 2 × ℂ => t.1) analyticAt_fst).add
    (hs.comp (f := fun t : Coeff 2 × ℂ => (t.2-(freeHillValue m:ℂ))/(m:ℂ))
      ((analyticAt_snd.sub analyticAt_const).div_const))

theorem hillAbelianHilbertRootEnergy_update_same (m : ℕ) (hm : 1 ≤ m) (a : Coeff 2) (s : ℂ) :
    hillAbelianHilbertRootEnergy (hillAbelianRootUpdate m (a,s)) m = s := by
  have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [hillAbelianHilbertRootEnergy,hillAbelianRootUpdate_apply_same]
  field_simp
  ring

theorem hillAbelianHilbertRootEnergy_update_other (m j : ℕ) (hj : j ≠ m) (a : Coeff 2) (s : ℂ) :
    hillAbelianHilbertRootEnergy (hillAbelianRootUpdate m (a,s)) j = hillAbelianHilbertRootEnergy a j := by
  rw [hillAbelianHilbertRootEnergy,hillAbelianHilbertRootEnergy,
    hillAbelianRootUpdate_apply_other m a s (j:ℤ) (by exact_mod_cast hj)]

theorem hillAbelianRootUpdate_star (m : ℕ) (a : Coeff 2) (s : ℂ) :
    hillAbelianRootUpdate m (star a,conj s) = star (hillAbelianRootUpdate m (a,s)) := by
  ext j
  by_cases hj : j = (m:ℤ)
  · subst j
    rw [lp.star_apply,hillAbelianRootUpdate_apply_same,hillAbelianRootUpdate_apply_same,Complex.star_def]
    simp only [map_div₀,map_sub,conj_ofReal,map_natCast]
  · rw [lp.star_apply,hillAbelianRootUpdate_apply_other _ _ _ _ hj,
      hillAbelianRootUpdate_apply_other _ _ _ _ hj,lp.star_apply]

end NLS.KdV
