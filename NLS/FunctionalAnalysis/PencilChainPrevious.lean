import NLS.FunctionalAnalysis.PencilChainEquations

/-! # The preceding full-domain coefficient of a finite pencil chain -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {D E : Type*} [AddCommGroup D] [Module ℂ D] [AddCommGroup E] [Module ℂ E]

/-- The preceding domain coefficient; the first coefficient has zero predecessor. -/
def pencilChainPrevious {N : ℕ} (v : Fin N → D) (k : Fin N) : D :=
  if h : k.val = 0 then 0 else v ⟨k.val-1, by omega⟩

omit [Module ℂ D] in
theorem pencilChainPrevious_zero {N : ℕ} (v : Fin N → D) (hN : 0 < N) :
    pencilChainPrevious v ⟨0,hN⟩ = 0 := by simp [pencilChainPrevious]

omit [Module ℂ D] in
theorem pencilChainPrevious_succ {N : ℕ} (v : Fin N → D) (k : ℕ) (hk : k+1 < N) :
    pencilChainPrevious v ⟨k+1,hk⟩ = v ⟨k,Nat.lt_trans (Nat.lt_succ_self k) hk⟩ := by
  simp [pencilChainPrevious]

/-- Every actual finite-chain coefficient satisfies its single predecessor equation. -/
theorem mem_pencilChainSpace_iff_previous (J P : D →ₗ[ℂ] E) (N : ℕ) (v : Fin N → D) :
    v ∈ pencilChainSpace J P N ↔ ∀ k : Fin N, P (v k) = J (pencilChainPrevious v k) := by
  rw [mem_pencilChainSpace_iff_equations]
  constructor
  · rintro ⟨h0,hs⟩ ⟨n,hn⟩
    cases n with
    | zero => rw [pencilChainPrevious_zero, map_zero]; exact h0 hn
    | succ n => rw [pencilChainPrevious_succ]; exact hs n hn
  · intro h
    constructor
    · intro hN
      simpa only [pencilChainPrevious_zero, map_zero] using h ⟨0,hN⟩
    · intro k hk
      simpa only [pencilChainPrevious_succ] using h ⟨k+1,hk⟩

end NLS.FunctionalAnalysis
