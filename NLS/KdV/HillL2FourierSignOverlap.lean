import NLS.SequenceSpaces.BoundedDiagonalSignRigidity
import NLS.SequenceSpaces.WeightedAffineSigns
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.KdV.HillFreeAmplitudeGrowth

/-! Two ORIGINAL L2 Fourier packet decompositions of the SAME actual
map have eventually identical positive physical output signs. -/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.KdV

theorem eventually_eq_hill_l2_fourier_signs
    (U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)) (hU : IsOpen U)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2) (hq : q∈U)
    (e d : ℤ → Bool)
    (G : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → ℕ+ → ℂ)
    (R S : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 2) 2)
    (CR CS : ℝ) (hR : ∀ p∈U,‖R p‖≤CR) (hS : ∀ p∈U,‖S p‖≤CS)
    (hG : ∀ p∈U,∀ n : ℕ+,G p n=if e (n:ℤ) then
      -((hillL2FreeAmplitude n:ℂ)/(1+(n:ℂ))*p.val (n:ℤ)+(R p).val (n:ℤ))
      else (hillL2FreeAmplitude n:ℂ)/(1+(n:ℂ))*p.val (n:ℤ)+(R p).val (n:ℤ))
    (hG' : ∀ p∈U,∀ n : ℕ+,G p n=if d (n:ℤ) then
      -((hillL2FreeAmplitude n:ℂ)/(1+(n:ℂ))*p.val (n:ℤ)+(S p).val (n:ℤ))
      else (hillL2FreeAmplitude n:ℂ)/(1+(n:ℂ))*p.val (n:ℤ)+(S p).val (n:ℤ)) :
    ∀ᶠ k : ℕ in atTop,e ((k+1:ℕ):ℤ)=d ((k+1:ℕ):ℤ) := by
  let n := fun k : ℕ => (⟨k+1,Nat.succ_pos k⟩ : ℕ+)
  let a := fun k => (1+(n k:ℝ))*hillL2FreeAmplitude (n k)
  let L := fun k => WeightedCoeff.evalCLM (Weight.sobolev ((1:ℝ)-1)) 2 (n k:ℤ)
  let v := fun k => WeightedCoeff.single (p := 2) (Weight.sobolev ((1:ℝ)-1)) (n k:ℤ) 1
  let f := fun k p => (Weight.sobolev 2 (n k:ℤ):ℂ)*
    ((if d (n k:ℤ) then -(S p).val (n k:ℤ) else (S p).val (n k:ℤ))-
      (if e (n k:ℤ) then -(R p).val (n k:ℤ) else (R p).val (n k:ℤ)))
  have hwbound (A : WeightedCoeff (Weight.sobolev 2) 2) (C : ℝ) (hA : ‖A‖≤C) (j : ℤ) :
      Weight.sobolev 2 j*‖A.val j‖≤C := by
    have h := (le_div_iff₀ ((Weight.sobolev 2).positive j)).mp (WeightedCoeff.norm_apply_le _ 2 A j)
    nlinarith
  apply eventually_eq_signs_of_bounded_diagonal_error atTop a (fun k => mul_nonneg (by positivity) (hillL2FreeAmplitude_pos (n k)).le)
    (by simpa only [a,n] using tendsto_hillL2FreeAmplitude_bracket)
    (fun k => e (n k:ℤ)) (fun k => d (n k:ℤ)) L v
    (fun k => by simp [v,WeightedCoeff.norm_single,Weight.sobolev_apply])
    (fun k => by simp [L,v,WeightedCoeff.evalCLM_apply,WeightedCoeff.single_val]) U hU q hq f (CR+CS)
  · intro k p hp
    change ‖(Weight.sobolev 2 (n k:ℤ):ℂ)*_‖≤_
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev 2).positive _).le]
    apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) ((Weight.sobolev 2).positive _).le).trans
    rw [mul_add]
    have hr := hwbound (R p) CR (hR p hp) (n k:ℤ)
    have hs := hwbound (S p) CS (hS p hp) (n k:ℤ)
    cases e (n k:ℤ) <;> cases d (n k:ℤ) <;> simp only [Bool.false_eq_true,↓reduceIte,norm_neg] <;> linarith
  · intro k p hp
    have he := (hG p hp (n k)).symm.trans (hG' p hp (n k))
    have hw : (Weight.sobolev 2 (n k:ℤ):ℂ)=(1+(n k:ℂ))^2 := by
      simp only [Weight.sobolev_apply,Real.rpow_two,Int.cast_natCast,
        abs_of_pos (by positivity : (0:ℝ)<n k),Complex.ofReal_pow,Complex.ofReal_add,
        Complex.ofReal_one,Complex.ofReal_natCast]
    change (Weight.sobolev 2 (n k:ℤ):ℂ)*_=_
    rw [hw]
    simp only [a,L,WeightedCoeff.evalCLM_apply,Complex.ofReal_mul,Complex.ofReal_add,
      Complex.ofReal_one,Complex.ofReal_natCast]
    have hne : 1+(n k:ℂ)≠0 := by exact_mod_cast (show 1+(n k:ℝ)≠0 by positivity)
    exact weighted_affine_sign_error (1+(n k:ℂ)) (hillL2FreeAmplitude (n k):ℂ)
      (p.val (n k:ℤ)) ((R p).val (n k:ℤ)) ((S p).val (n k:ℤ)) hne (e (n k:ℤ)) (d (n k:ℤ)) he

end NLS.KdV
