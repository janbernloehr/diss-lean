import NLS.SequenceSpaces.SignedHalfOrderTarget

/-! An exact real positive Fourier multiplier determines BOTH signed
halves of its original-source completion, including the zero coefficient. -/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.WeightedCoeff

theorem signedHalfTarget_exact_fourier_core (v : Weight) (hv : ∀ j,v (-j)=v j)
    (U : Set (WeightedCoeff v 2)) (e : ℤ → Bool)
    (A : WeightedCoeff v 2 → WeightedCoeff (Weight.sobolev 1) 2)
    (c d : ℕ+ → ℝ) (hd : ∀ n : ℕ+,Weight.sobolev (1/2) (n:ℤ)*c n=d n)
    (hAh : ∀ p∈U,∀ j : ℤ,j≤0 → (A p).val j=0)
    (hAc : ∀ p∈U,∀ n : ℕ+,(A p).val (n:ℤ)=(c n:ℂ)*p.val (n:ℤ))
    (p : WeightedCoeff v 2) (hp : p∈U) (hJp : conjugateReflection v hv p∈U) :
    (signedHalfTarget v 1 e A p).val 0=0 ∧ ∀ n : ℕ+,
      (signedHalfTarget v 1 e A p).val (n:ℤ)=
        (if e (n:ℤ) then -((d n:ℂ)*p.val (n:ℤ)) else (d n:ℂ)*p.val (n:ℤ)) ∧
      (signedHalfTarget v 1 e A p).val (-(n:ℤ))=
        (if e (n:ℤ) then -((d n:ℂ)*p.val (-(n:ℤ))) else (d n:ℂ)*p.val (-(n:ℤ))) := by
  have hc (n : ℕ+) : (Weight.sobolev (1/2) (n:ℤ):ℂ)*(c n:ℂ)=(d n:ℂ) := by
    exact_mod_cast hd n
  have he (z) (hz : z∈U) (n : ℕ+) : (Weight.sobolev (1/2) (n:ℤ):ℂ)*(A z).val (n:ℤ)=
      (d n:ℂ)*z.val (n:ℤ) := by
    rw [hAc z hz n,←mul_assoc,hc]
  constructor
  · rw [signedHalfTarget_apply v hv]
    simp only [neg_zero,hAh p hp 0 le_rfl,hAh _ hJp 0 le_rfl,neg_zero,ite_self,map_zero,add_zero,mul_zero]
  intro n
  have hn : -(n:ℤ)≤0 := neg_nonpos.mpr (le_of_lt (by exact_mod_cast n.pos : (0:ℤ)<n))
  constructor
  · rw [signedHalfTarget_apply v hv,hAh _ hJp _ hn]
    simp only [neg_zero,ite_self,map_zero,add_zero]
    split_ifs <;> simp only [mul_neg,he p hp n]
  · rw [signedHalfTarget_apply v hv,hAh p hp _ hn]
    simp only [neg_zero,ite_self,zero_add,neg_neg,Weight.sobolev_neg]
    have hm (z : ℂ) : (Weight.sobolev (1/2) (n:ℤ):ℂ)*conj z=
        conj ((Weight.sobolev (1/2) (n:ℤ):ℂ)*z) := by
      simp only [map_mul,conj_ofReal]
    rw [hm]
    split_ifs <;> simp only [mul_neg,he _ hJp n,map_neg,map_mul,conj_ofReal,
      conjugateReflection_apply,map_mul,conj_ofReal,conj_conj]

end NLS.WeightedCoeff
