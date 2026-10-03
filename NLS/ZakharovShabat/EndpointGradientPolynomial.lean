import NLS.ZakharovShabat.ClassicalSeparatedGradient
import Mathlib.Tactic.FinCases

/-! # Stability of the endpoint-gradient polynomial

Three solution values and the two terminal columns determine every
linear endpoint gradient. The estimate retains a single small factor
when these five vectors are replaced by nearby reference values.
-/

noncomputable section
open Complex
namespace NLS.ZakharovShabat

/-- The actual gradient formula as a polynomial in its five solution values. -/
def endpointGradientPolynomial (L : (ℂ × ℂ) →L[ℂ] ℂ) (a : Fin 5 → ℂ × ℂ) : ℂ × ℂ :=
  (I*(L (a 3)*(a 1).2-L (a 4)*(a 0).2)*(a 2).2,
   I*(L (a 3)*(a 1).1-L (a 4)*(a 0).1)*(a 2).1)

private theorem norm_triple_sub_le (a b c x y z : ℂ) (E D : ℝ)
    (hE : 0 ≤ E) (hD : 0 ≤ D)
    (_ha : ‖a‖ ≤ E) (hb : ‖b‖ ≤ E) (hc : ‖c‖ ≤ E)
    (hx : ‖x‖ ≤ E) (hy : ‖y‖ ≤ E) (_hz : ‖z‖ ≤ E)
    (hax : ‖a-x‖ ≤ D) (hby : ‖b-y‖ ≤ D) (hcz : ‖c-z‖ ≤ D) :
    ‖a*b*c-x*y*z‖ ≤ 3*E^2*D := by
  have he : a*b*c-x*y*z = (a-x)*b*c+x*(b-y)*c+x*y*(c-z) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_mul]
  calc
    _ ≤ D*E*E+E*D*E+E*E*D := by gcongr
    _ = _ := by ring

/-- A uniform Lipschitz bound for the actual cubic endpoint-gradient expression. -/
theorem norm_endpointGradientPolynomial_sub_le
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (a b : Fin 5 → ℂ × ℂ) (E D : ℝ) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (ha : ∀ i, ‖a i‖ ≤ E) (hb : ∀ i, ‖b i‖ ≤ E)
    (hab : ∀ i, ‖a i-b i‖ ≤ D) :
    ‖endpointGradientPolynomial L a-endpointGradientPolynomial L b‖ ≤ 6*E^2*D := by
  have hobs (v : ℂ × ℂ) : ‖L v‖ ≤ ‖v‖ :=
    (L.le_opNorm v).trans (by simpa using mul_le_mul_of_nonneg_right hL (norm_nonneg v))
  have hobsdiff (i : Fin 5) : ‖L (a i)-L (b i)‖ ≤ D := by
    rw [← map_sub]
    exact (hobs _).trans (hab i)
  have hpart (k j : Fin 5) (P : (ℂ × ℂ) →L[ℂ] ℂ) (hP : ∀ v, ‖P v‖ ≤ ‖v‖) :
      ‖L (a k)*P (a j)*P (a 2)-L (b k)*P (b j)*P (b 2)‖ ≤ 3*E^2*D := by
    apply norm_triple_sub_le _ _ _ _ _ _ E D hE hD
      ((hobs _).trans (ha k)) ((hP _).trans (ha j)) ((hP _).trans (ha 2))
      ((hobs _).trans (hb k)) ((hP _).trans (hb j)) ((hP _).trans (hb 2))
      (hobsdiff k)
    · rw [← map_sub]; exact (hP _).trans (hab j)
    · rw [← map_sub]; exact (hP _).trans (hab 2)
  have hcomponent (P : (ℂ × ℂ) →L[ℂ] ℂ) (hP : ∀ v, ‖P v‖ ≤ ‖v‖) :
      ‖I*(L (a 3)*P (a 1)-L (a 4)*P (a 0))*P (a 2)-
        I*(L (b 3)*P (b 1)-L (b 4)*P (b 0))*P (b 2)‖ ≤ 6*E^2*D := by
    have he : I*(L (a 3)*P (a 1)-L (a 4)*P (a 0))*P (a 2)-
        I*(L (b 3)*P (b 1)-L (b 4)*P (b 0))*P (b 2) =
        I*((L (a 3)*P (a 1)*P (a 2)-L (b 3)*P (b 1)*P (b 2))-
          (L (a 4)*P (a 0)*P (a 2)-L (b 4)*P (b 0)*P (b 2))) := by ring
    rw [he,norm_mul,norm_I,one_mul]
    exact (norm_sub_le _ _).trans ((add_le_add (hpart 3 1 P hP) (hpart 4 0 P hP)).trans_eq (by ring))
  apply norm_prod_le_iff.mpr
  exact ⟨hcomponent (ContinuousLinearMap.snd ℂ ℂ ℂ) norm_snd_le,
    hcomponent (ContinuousLinearMap.fst ℂ ℂ ℂ) norm_fst_le⟩

end NLS.ZakharovShabat
