import NLS.ZakharovShabat.SourcePsiOriginalFamilyQuotient
import NLS.ZakharovShabat.SourceAngularEtaDiagonalBound
import NLS.ZakharovShabat.SourceAngularOriginalThetaDomain

/-!
# Original diagonal eta numerator bounds

One local constant bounds every diagonal numerator on its original disk,
at any complex source. Filling the omitted root with its midpoint leaves
the deleted product unchanged, so the original family quotient estimate applies.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One local constant controls every diagonal numerator on all original disks. -/
theorem angular_original_diagonal_bound (H : SourceLemma12_12Data hp hp1 W₀ W s)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hφV : φ ∈ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∩ V ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ∀ n : ℤ, ∀ z ∈ D n,
        ‖sourceAngularGapNumerator hp hp1 n n s ψ z-I‖ ≤ M := by
  obtain ⟨U,hU,hφU,hUV,M,hM,hquot⟩ := H.previous.original_allDisk_quotient_errorBound hD hV φ hφ hφV
  refine ⟨U,hU,hφU,hUV,M,hM,?_⟩
  intro ψ hψ n z hz
  obtain ⟨E,hE,_,hbound⟩ := hquot ψ hψ n
  let b := sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)
  have hfill : sourcePsiCandidate n (z,b) = sourcePsiCandidate n (z,(s n ψ : Coeff p)) :=
    sourcePsiCandidate_eq_of_off_index hp hp1 n z b _
      (fun k hk => sourcePsiFillDeletedRoot_apply_other n k hk (s n ψ) _)
  have hprod : jointDeletedSingleSpectralProduct n (z,b) =
      jointDeletedSingleSpectralProduct n (z,(s n ψ : Coeff p)) := by
    dsimp only [sourcePsiCandidate] at hfill
    exact mul_left_cancel₀ (by norm_num : (-2:ℂ) ≠ 0) hfill
  have hq : sourceSingleRootQuotientJointProduct hp hp1 n (z,((s n ψ : Coeff p),ψ)) =
      sourceSingleRootQuotientJointProduct hp hp1 n (z,(b,ψ)) := by
    simp only [sourceSingleRootQuotientJointProduct,hprod]
  rw [sourceAngularGapNumerator_diagonal_eq_quotient,hq,
    show I*sourceSingleRootQuotientJointProduct hp hp1 n (z,(b,ψ))-I =
      I*(sourceSingleRootQuotientJointProduct hp hp1 n (z,(b,ψ))-1) by ring,
    norm_mul,norm_I,one_mul]
  exact (hbound n z hz).trans ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' E n).trans hE)

end SourceLemma12_12Data
end NLS.ZakharovShabat
