import NLS.MKdV.MiuraRealL2ActionMap
import NLS.ZakharovShabat.SourceDiagonalLaurentCoefficientContinuity

/-! # Weak Fourier continuity of the actual scalar mKdV actions

The literal diagonal source is bounded whenever the scalar L² family is
bounded. The actual inverse-frequency spectral action then converges at
every positive index under bounded coefficient limits.
-/
noncomputable section
open Set Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem tendsto_miuraL2Action_of_bounded_coefficientwise
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated]
    (a : A → MiuraRealL2) (b : MiuraRealL2) (hb : Bornology.IsBounded (range a))
    (ht : ∀ n : ℤ, Tendsto (fun k => (a k).val n) l (𝓝 (b.val n))) (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun k => miuraL2Action n (a k).val) l (𝓝 (miuraL2Action n b.val)) := by
  obtain ⟨M,hM⟩ := hb.exists_norm_le
  have hbd : Bornology.IsBounded (range (fun k => scalarL2Diagonal (a k).val)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖scalarL2Diagonal‖*M,?_⟩
    rintro _ ⟨k,rfl⟩
    exact (scalarL2Diagonal.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM _ ⟨k,rfl⟩) (norm_nonneg _))
  have hd (u : MiuraRealL2) : scalarL2Diagonal u.val ∈ realDiagonalSourceLocus 2 := by
    constructor
    · intro j
      change (scalarL2Diagonal u.val).snd j = conj ((scalarL2Diagonal u.val).fst (-j))
      rw [scalarL2Diagonal_fst,scalarL2Diagonal_snd]
      exact u.property j
    · rw [scalarL2Diagonal_fst,scalarL2Diagonal_snd]
  exact (tendsto_sourceDiagonalLaurentAction_zero_of_bounded_coefficientwise
    (fun k => scalarL2Diagonal (a k).val) (scalarL2Diagonal b.val) hbd
    (fun k => hd (a k)) (hd b) (by intro j; simpa only [scalarL2Diagonal_fst] using ht j)
    n (by omega)).const_mul (1/2 : ℂ)

end NLS.MKdV
