import NLS.FunctionalAnalysis.PencilRootChains

/-! # Coefficientwise equations of complete finite domain chains -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {D E : Type*} [AddCommGroup D] [Module ℂ D] [AddCommGroup E] [Module ℂ E]

/-- The recursive full-domain chain condition is exactly the first
eigenvector equation and every consecutive associated-vector equation. -/
theorem mem_pencilChainSpace_iff_equations (J P : D →ₗ[ℂ] E) (N : ℕ) :
    ∀ v : Fin N → D, v ∈ pencilChainSpace J P N ↔
      (∀ hN : 0 < N, P (v ⟨0,hN⟩) = 0) ∧
      ∀ (k : ℕ) (hk : k+1 < N), P (v ⟨k+1,hk⟩) =
        J (v ⟨k,Nat.lt_trans (Nat.lt_succ_self k) hk⟩) := by
  induction N with
  | zero =>
    intro v
    constructor
    · intro _
      constructor
      · intro hN
        omega
      · intro k hk
        omega
    · intro _
      exact Submodule.mem_top
  | succ N ih =>
    intro v
    rw [mem_pencilChainSpace_succ]
    constructor
    · rintro ⟨hv, hlast⟩
      constructor
      · intro hN
        cases N with
        | zero => simpa only [pencilChainEndpoint_zero] using! hlast
        | succ m => exact ((ih (Fin.init v)).mp hv).1 (Nat.zero_lt_succ m)
      · intro k hk
        cases N with
        | zero => omega
        | succ m =>
          by_cases hm : k+1 < m+1
          · exact ((ih (Fin.init v)).mp hv).2 k hm
          · have hkm : k = m := by omega
            subst k
            simpa only [pencilChainEndpoint_succ] using! hlast
    · rintro ⟨hfirst, hnext⟩
      refine ⟨(ih (Fin.init v)).mpr ⟨?_, ?_⟩, ?_⟩
      · intro hN
        exact hfirst (Nat.lt_trans hN (Nat.lt_succ_self N))
      · intro k hk
        exact hnext k (Nat.lt_trans hk (Nat.lt_succ_self N))
      · cases N with
        | zero => simpa only [pencilChainEndpoint_zero] using! hfirst (by norm_num)
        | succ m =>
          simpa only [pencilChainEndpoint_succ] using! hnext m (Nat.lt_succ_self (m+1))

end NLS.FunctionalAnalysis
