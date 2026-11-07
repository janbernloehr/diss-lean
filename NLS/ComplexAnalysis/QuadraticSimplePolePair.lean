import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Pairing opposite simple poles after odd quadratic descent. The
normalization retains the two frequency derivatives in an energy pole. -/
noncomputable section
namespace NLS.ComplexAnalysis

theorem sum_opposite_evaluations_simple_pole (A D μ w : ℂ)
    (hD : D ≠ 0) (hw : w ≠ μ) (hwn : w ≠ -μ) :
    A/D/(w-μ)+A/D/(-w-μ) = (2*μ*A)/(D*(w^2-μ^2)) := by
  have hm : w-μ ≠ 0 := sub_ne_zero.mpr hw
  have hp : w+μ ≠ 0 := by intro he; apply hwn; linear_combination he
  have hn : -w-μ ≠ 0 := by intro he; apply hwn; linear_combination -he
  have hq : w^2-μ^2 ≠ 0 := by rw [sq_sub_sq]; exact mul_ne_zero hp hm
  field_simp [hD,hm,hp,hn,hq]
  ring

theorem weighted_opposite_simple_pole_pairs (A B μ d w s p : ℂ)
    (hμ : μ ≠ 0) (hd : d ≠ 0) (hw : w ≠ μ) (hwn : w ≠ -μ)
    (hAB : A-B=2*μ*p) :
    (s/2)*((A/(2*μ^2*d)/(w-μ)+A/(2*μ^2*d)/(-w-μ))+
      (B/(2*μ^2*d)/(w+μ)+B/(2*μ^2*d)/(-w+μ))) = p*s/(d*(w^2-μ^2)) := by
  have hD : 2*μ^2*d ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hμ)) hd
  have hpos := sum_opposite_evaluations_simple_pole A (2*μ^2*d) μ w hD hw hwn
  have hneg := sum_opposite_evaluations_simple_pole B (2*μ^2*d) (-μ) w hD hwn (by simpa using hw)
  simp only [sub_neg_eq_add,neg_sq] at hneg
  rw [hpos,hneg]
  have hm : w-μ ≠ 0 := sub_ne_zero.mpr hw
  have hp : w+μ ≠ 0 := by intro he; apply hwn; linear_combination he
  have hq : w^2-μ^2 ≠ 0 := by rw [sq_sub_sq]; exact mul_ne_zero hp hm
  have hA : A=B+2*μ*p := by linear_combination hAB
  rw [hA]
  field_simp [hμ,hd,hq]
  ring

end NLS.ComplexAnalysis
