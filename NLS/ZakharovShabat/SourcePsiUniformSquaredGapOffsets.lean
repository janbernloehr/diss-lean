import NLS.ZakharovShabat.SourcePsiActualTailRootOffset
import NLS.ZakharovShabat.SourcePsiFiniteHeadRootOffset

/-!
# All-index uniform lp squared-gap offsets for actual psi branches

Patch the finite head with its uniform quadratic-gap bound and keep
the actual lp tail majorant elsewhere. The patched sequence has a
common norm bound independent of the omitted index. Literal division
by the squared gaps gives an lp offset sequence and exact root
factorization, including zero gaps, on one complex neighborhood of
each real source.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourcePsiIsolatingComplexRootAtlas.exists_local_uniform_squared_gap_offsets
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
    (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U) (φ : realTypeSourceLocus p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
      V ⊆ A.toSourcePsiComplexRootAtlas.sourceBall φ ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ V, ∀ n : ℤ, ∃ α : Coeff p,
        α n = 0 ∧
        (∀ m, m ≠ n → displacedRoots (A.toSourcePsiComplexRootAtlas.branch n ψ : Coeff p) m =
          sourceStandardRootMidpoint hp hp1 ψ m + (sourcePeriodicGapDisplacement hp hp1 ψ m)^2*α m) ∧
        ‖α‖ ≤ C := by
  classical
  let B := A.toSourcePsiComplexRootAtlas
  obtain ⟨Vt,hVt,hφVt,hVtBall,K,Ct,hCt,htail⟩ := A.exists_local_tail_squared_offset_majorant φ
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  obtain ⟨Vh,hVh,hφVh,_,Ch,hCh,hhead⟩ := A.exists_local_finiteHead_squared_offset_bound φ s
  let V := Vt ∩ Vh
  let C := s.card*Ch+Ct
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨V,hVt.inter hVh,⟨hφVt,hφVh⟩,(fun ψ hψ => hVtBall hψ.1),C,hC,?_⟩
  intro ψ hψ n
  obtain ⟨E,hE,hEpoint⟩ := htail ψ hψ.1 n
  let b : ℤ → ℂ := fun m => if m ∈ s then (Ch : ℂ) else E m
  have hb : Memℓp b p := NLS.memℓp_of_eq_outside_finset (lp.memℓp E) s (by
    intro m hm
    simp only [b,if_neg hm])
  let F : Coeff p := ⟨b,hb⟩
  have hFhead m (hm : m ∈ s) : ‖F m‖ = Ch := by
    simp only [F,b,if_pos hm,Complex.norm_real,Real.norm_of_nonneg hCh]
  have hFtail m (hm : m ∉ s) : F m = E m := by simp only [F,b,if_neg hm]
  have hFnorm : ‖F‖ ≤ C := by
    calc
      ‖F‖ ≤ s.card*Ch+‖E‖ := NLS.Coeff.norm_le_of_eq_outside_finset F E s Ch
        (fun m hm => (hFhead m hm).le) hFtail
      _ ≤ C := by dsimp [C]; exact add_le_add le_rfl hE
  have hpoint m (hmn : m ≠ n) :
      ‖displacedRoots (B.branch n ψ : Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤
        1*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2*‖F m‖ := by
    rw [one_mul]
    by_cases hm : m ∈ s
    · rw [hFhead m hm,mul_comm]
      exact hhead ψ hψ.2 n m hm hmn
    · rw [hFtail m hm]
      have hmK : K ≤ m.natAbs := by simp only [s,Finset.mem_Icc] at hm; omega
      exact hEpoint m hmK hmn
  obtain ⟨α,hαn,hfactor,hαnorm⟩ := exists_sourcePsi_squared_gap_offsets_of_majorant
    hp hp1 n (B.branch n ψ) ψ F 1 (by norm_num) hpoint
  have hαF : ‖α‖ ≤ ‖F‖ := by simpa only [one_mul] using hαnorm
  exact ⟨α,hαn,hfactor,hαF.trans hFnorm⟩

end NLS.ZakharovShabat
