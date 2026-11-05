import NLS.SequenceSpaces.FourierRealModePlane

/-! Comparing literal native action products along two physical mode lines. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem fourierRealModeLine_apply (w : Weight) (hw : ∀ k, w (-k)=w k) (n : ℕ+)
    (z : fourierRealZeroSubmodule w p) (c : ℂ) (t : ℝ) (k : ℤ) :
    (z+t • fourierRealModeCLM w hw n c).val.val.val k=z.val.val.val k+
      (t:ℂ)*((if k=(n:ℤ) then c else 0)+(if k=-(n:ℤ) then (starRingEnd ℂ) c else 0)) := by
  change z.val.val.val k+(t:ℂ)*(fourierRealModeCLM w hw n c).val.val.val k=_
  rw [fourierRealModeCLM_apply]

theorem fourierRealModeLine_products (w : Weight) (hw : ∀ k, w (-k)=w k) (n : ℕ+)
    (u z : fourierRealZeroSubmodule w p) (a b : ℂ) (t : ℝ)
    (hbase : ∀ m : ℕ+, u.val.val.val (m:ℤ)*u.val.val.val (-(m:ℤ))=
      z.val.val.val (m:ℤ)*z.val.val.val (-(m:ℤ)))
    (hselected : (u.val.val.val (n:ℤ)+(t:ℂ)*a)*
        (starRingEnd ℂ) (u.val.val.val (n:ℤ)+(t:ℂ)*a)=
      (z.val.val.val (n:ℤ)+(t:ℂ)*b)*(starRingEnd ℂ) (z.val.val.val (n:ℤ)+(t:ℂ)*b))
    (m : ℕ+) :
    (u+t • fourierRealModeCLM w hw n a).val.val.val (m:ℤ)*
      (u+t • fourierRealModeCLM w hw n a).val.val.val (-(m:ℤ))=
    (z+t • fourierRealModeCLM w hw n b).val.val.val (m:ℤ)*
      (z+t • fourierRealModeCLM w hw n b).val.val.val (-(m:ℤ)) := by
  have hn : (0:ℤ)<n := by exact_mod_cast n.pos
  have hm : (0:ℤ)<m := by exact_mod_cast m.pos
  simp only [fourierRealModeLine_apply]
  by_cases h : (m:ℤ)=(n:ℤ)
  · have hneg : -(n:ℤ)≠(n:ℤ) := by omega
    simpa only [h,ite_true,if_neg hneg,if_neg (Ne.symm hneg),add_zero,zero_add,u.property (n:ℤ),z.property (n:ℤ),
      map_add,map_mul,Complex.conj_ofReal] using hselected
  · have h1 : (m:ℤ)≠-(n:ℤ) := by omega
    have h2 : -(m:ℤ)≠(n:ℤ) := by omega
    have h3 : -(m:ℤ)≠-(n:ℤ) := by omega
    simpa only [if_neg h,if_neg h1,if_neg h2,if_neg h3,add_zero,mul_zero] using hbase m

end NLS.WeightedCoeff
