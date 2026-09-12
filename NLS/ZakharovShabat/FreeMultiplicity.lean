import NLS.ZakharovShabat.RootSpaces

/-!
# Multiplicity of the free periodic eigenvalues

At `π n`, every generalized free eigenvector is supported at raw frequency `-n`
in the first component and `n` in the second. Thus there are no longer Jordan
chains and the full root space has complex dimension two.
-/

noncomputable section
open scoped ENNReal

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Insert the two coefficients of the signed free modes at eigenvalue `π n`. -/
def freeModeEmbedding (n : ℤ) : (ℂ × ℂ) →L[ℂ] PairSpace p :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p (-n)).prodMap
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n)

@[simp] theorem freeModeEmbedding_apply (n : ℤ) (a : ℂ × ℂ) :
    freeModeEmbedding (p := p) n a = (lp.single p (-n) a.1, lp.single p n a.2) := rfl

/-- The two signed free modes are linearly independent, including at `n = 0`. -/
theorem freeModeEmbedding_injective (n : ℤ) :
    Function.Injective (freeModeEmbedding (p := p) n) := by
  intro a b h
  have h₁ := congrArg (fun x : PairSpace p => x.1 (-n)) h
  have h₂ := congrArg (fun x : PairSpace p => x.2 n) h
  exact Prod.ext (by simpa using h₁) (by simpa using h₂)

/-- Every finite free root chain has only the two resonant Fourier coefficients. -/
theorem free_root_support (hp : p ≠ ⊤) (n : ℤ) (m : ℕ) (x : PairSpace p)
    (hx : x ∈ periodicRootSpace hp 0 ((Real.pi : ℂ) * n) m) :
    (∀ k, k ≠ -n → x.1 k = 0) ∧ (∀ k, k ≠ n → x.2 k = 0) := by
  induction m generalizing x with
  | zero =>
    have hx0 : x = 0 := hx
    simp [hx0]
  | succ m ih =>
    obtain ⟨f, rfl, hf⟩ := (mem_periodicRootSpace_succ hp 0 _ m x).mp hx
    obtain ⟨h₁, h₂⟩ := ih _ hf
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    constructor
    · intro k hk
      have he := h₁ k hk
      have hnk : (n : ℂ) + k ≠ 0 := by
        intro h
        have : n + k = 0 := by exact_mod_cast h
        omega
      simp only [domainInclusion_apply, scalarInclusion_apply]
      change f.1.val k = 0
      have he' : (Real.pi : ℂ) * ((n : ℂ) + k) * f.1.val k = 0 := by
        simpa only [spectralPencil_apply, operator_zero, Prod.fst_sub, Prod.smul_fst,
          lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, domainInclusion_apply, scalarInclusion_apply,
          freeOperator_fst_apply, sub_neg_eq_add, neg_mul, neg_neg, mul_add, add_mul] using he
      exact (mul_eq_zero.mp he').resolve_left (mul_ne_zero hπ hnk)
    · intro k hk
      have he := h₂ k hk
      have hnk : (n : ℂ) - k ≠ 0 := by
        intro h
        have : n - k = 0 := by exact_mod_cast h
        omega
      simp only [domainInclusion_apply, scalarInclusion_apply]
      change f.2.val k = 0
      have he' : (Real.pi : ℂ) * ((n : ℂ) - k) * f.2.val k = 0 := by
        simpa only [spectralPencil_apply, operator_zero, Prod.snd_sub, Prod.smul_snd,
          lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, domainInclusion_apply, scalarInclusion_apply,
          freeOperator_snd_apply, mul_sub, sub_mul] using he
      exact (mul_eq_zero.mp he').resolve_left (mul_ne_zero hπ hnk)

/-- Inserting any two resonant coefficients gives an ordinary free eigenvector. -/
theorem freeModeEmbedding_mem_root_one (hp : p ≠ ⊤) (n : ℤ) (a : ℂ × ℂ) :
    freeModeEmbedding (p := p) n a ∈ periodicRootSpace hp 0 ((Real.pi : ℂ) * n) 1 := by
  rw [mem_periodicRootSpace_succ]
  refine ⟨(scalarMode (-n) a.1, scalarMode n a.2), by simp, ?_⟩
  change spectralPencil hp 0 _ _ = 0
  rw [spectralPencil_apply, operator_zero]
  apply Prod.ext <;> apply lp.ext <;> funext k
  · change ((Real.pi : ℂ) * n) * (domainInclusion _).1 k - (freeOperator _).1 k = 0
    by_cases hk : k = -n <;> simp [hk]
  · change ((Real.pi : ℂ) * n) * (domainInclusion _).2 k - (freeOperator _).2 k = 0
    by_cases hk : k = n <;> simp [hk]

/-- The full free root space consists exactly of the two signed modes. -/
theorem periodicRootSpaceTop_zero_eq_range (hp : p ≠ ⊤) (n : ℤ) :
    periodicRootSpaceTop (p := p) hp 0 ((Real.pi : ℂ) * n) =
      (freeModeEmbedding n).range := by
  apply le_antisymm
  · intro x hx
    obtain ⟨m, hm⟩ := (mem_periodicRootSpaceTop hp 0 _ x).mp hx
    obtain ⟨h₁, h₂⟩ := free_root_support hp n m x hm
    refine ⟨(x.1 (-n), x.2 n), ?_⟩
    apply Prod.ext <;> ext k
    · by_cases hk : k = -n <;> simp [lp.single_apply, hk, h₁ k]
    · by_cases hk : k = n <;> simp [lp.single_apply, hk, h₂ k]
  · rintro x ⟨a, rfl⟩
    exact (mem_periodicRootSpaceTop hp 0 _ _).mpr
      ⟨1, freeModeEmbedding_mem_root_one hp n a⟩

/-- Free generalized eigenvectors are already ordinary eigenvectors. -/
theorem periodicRootSpace_one_zero_eq_top (hp : p ≠ ⊤) (n : ℤ) :
    periodicRootSpace (p := p) hp 0 ((Real.pi : ℂ) * n) 1 =
      periodicRootSpaceTop hp 0 ((Real.pi : ℂ) * n) := by
  apply le_antisymm
  · intro x hx
    exact (mem_periodicRootSpaceTop hp 0 _ x).mpr ⟨1, hx⟩
  · rw [periodicRootSpaceTop_zero_eq_range]
    rintro x ⟨a, rfl⟩
    exact freeModeEmbedding_mem_root_one hp n a

/-- Each free periodic spectral value has algebraic multiplicity two. -/
theorem periodicAlgebraicMultiplicity_zero (hp : p ≠ ⊤) (n : ℤ) :
    periodicAlgebraicMultiplicity (p := p) hp 0 ((Real.pi : ℂ) * n) = 2 := by
  rw [periodicAlgebraicMultiplicity, periodicRootSpaceTop_zero_eq_range]
  have h := LinearMap.finrank_range_of_inj (freeModeEmbedding_injective (p := p) n)
  simpa using h

end NLS.ZakharovShabat
