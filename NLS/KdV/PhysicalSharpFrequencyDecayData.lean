import NLS.KdV.PhysicalSharpDiagonalCancellation

/-! Combining actual diagonal and off-diagonal estimates on one
physical chart. The source space and rough inclusion remain opaque. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

def PhysicalFrequencyParameterization.HasSharpFrequencyDecay
    (A : PhysicalFrequencyParameterization E t ht J) (q : E) : Prop :=
  ∃ T : Set E, IsOpen T ∧ q∈T ∧ T⊆A.domain ∧ ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
    (∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
      Weight.sobolev (3*t-1) (n:ℤ)*‖A.renormalizedCorrection n a‖≤M) ∧
    (t<2/3 → ∀ a∈T, Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) ((n+1:ℕ):ℤ)*
      ‖A.renormalizedCorrection ⟨n+1,by omega⟩ a‖) atTop (𝓝 0)) ∧
    ∀ a∈T, ∀ p : RealPeriodOneHillPotential, J a=hillOriginalHminusSource p.val →
      (∀ n : ℕ+, K≤(n:ℤ).natAbs → Weight.sobolev (3*t-1) (n:ℤ)*
        ‖A.physical.correction n (hillOriginalHminusSource p.val)+
          6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n:ℕ) 0 : ℂ)‖≤M) ∧
      (t<2/3 → Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) ((n+1:ℕ):ℤ)*
        ‖A.physical.correction ⟨n+1,by omega⟩ (hillOriginalHminusSource p.val)+
          6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n+1) 0 : ℂ)‖) atTop (𝓝 0))

theorem PhysicalFrequencyParameterization.sharpFrequencyDecay_of_parts
    (A : PhysicalFrequencyParameterization E t ht J) (q : E)
    (Td : Set E) (hTd : IsOpen Td) (hqTd : q∈Td) (hTdA : Td⊆A.domain)
    (K : ℕ) (Md : ℝ) (hMd : 0≤Md)
    (hdb : ∀ a∈Td, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
      Weight.sobolev (3*t-1) (n:ℤ)*‖A.diagonalRemainder n a‖≤Md)
    (hdt : ∀ a∈Td, Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) ((n+1:ℕ):ℤ)*
      ‖A.diagonalRemainder ⟨n+1,by omega⟩ a‖) atTop (𝓝 0))
    (To : Set E) (hTo : IsOpen To) (hqTo : q∈To) (Mo : ℝ) (hMo : 0≤Mo)
    (hob : ∀ a∈To, ∀ n : ℕ+, Weight.sobolev (3*t-1) (n:ℤ)*
      ‖A.physical.offDiagonalCorrection n (J a)‖≤Mo)
    (hot : t<2/3 → ∀ a∈To, Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) ((n+1:ℕ):ℤ)*
      ‖A.physical.offDiagonalCorrection ⟨n+1,by omega⟩ (J a)‖) atTop (𝓝 0)) :
    A.HasSharpFrequencyDecay q := by
  let T := Td∩To
  have hTA : T⊆A.domain := fun _ ha => hTdA ha.1
  have hsum (a : E) (n : ℕ+) :
      Weight.sobolev (3*t-1) (n:ℤ)*‖A.renormalizedCorrection n a‖≤
        Weight.sobolev (3*t-1) (n:ℤ)*‖A.diagonalRemainder n a‖+
          Weight.sobolev (3*t-1) (n:ℤ)*‖A.physical.offDiagonalCorrection n (J a)‖ := by
    have he : A.renormalizedCorrection n a=
        A.diagonalRemainder n a+A.physical.offDiagonalCorrection n (J a) := by
      exact (sub_add_cancel _ _).symm
    have h := mul_le_mul_of_nonneg_left (norm_add_le (A.diagonalRemainder n a)
      (A.physical.offDiagonalCorrection n (J a))) ((Weight.sobolev (3*t-1)).positive (n:ℤ)).le
    rw [← he,mul_add] at h
    exact h
  have hb : ∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
      Weight.sobolev (3*t-1) (n:ℤ)*‖A.renormalizedCorrection n a‖≤Md+Mo := by
    intro a ha n hn
    exact (hsum a n).trans (add_le_add (hdb a ha.1 n hn) (hob a ha.2 n))
  have hd : t<2/3 → ∀ a∈T, Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) ((n+1:ℕ):ℤ)*
      ‖A.renormalizedCorrection ⟨n+1,by omega⟩ a‖) atTop (𝓝 0) := by
    intro ht2 a ha
    have hlim := (hdt a ha.1).add (hot ht2 a ha.2)
    rw [add_zero] at hlim
    exact squeeze_zero' (Filter.Eventually.of_forall (fun n =>
      mul_nonneg ((Weight.sobolev (3*t-1)).positive _).le (norm_nonneg _)))
      (Filter.Eventually.of_forall (fun n => hsum a ⟨n+1,by omega⟩)) hlim
  refine ⟨T,hTd.inter hTo,⟨hqTd,hqTo⟩,hTA,K,Md+Mo,add_nonneg hMd hMo,hb,hd,?_⟩
  intro a ha p hp
  constructor
  · intro n hn
    simpa only [A.renormalizedCorrection_eq_original a (hTA ha) p hp] using hb a ha n hn
  · intro ht2
    exact Coeff.tendsto_positive_weighted_of_eq (Weight.sobolev (3*t-1))
      (fun n => A.renormalizedCorrection n a)
      (fun n => A.physical.correction n (hillOriginalHminusSource p.val)+
        6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n:ℕ) 0 : ℂ))
      (fun n => A.renormalizedCorrection_eq_original a (hTA ha) p hp n) (hd ht2 a ha)


end NLS.KdV
