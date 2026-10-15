import NLS.ZakharovShabat.SourceSection23Original
import NLS.ZakharovShabat.SourceIndexedHigherActionTrace
import NLS.ZakharovShabat.SourceIndexedHigherActionReal
import NLS.ZakharovShabat.SourceRealHigherActionIntegral
import NLS.ZakharovShabat.SourceHigherActionPiecewiseContour
import NLS.ZakharovShabat.SourceSection23TraceCorrections

/-! # Original Section 24 higher actions and physical traces

One original Birkhoff family and its unchanged Section 19/20 source domain
carry all higher actions and physical traces. The natural spectral power k
represents printed action level k+1. The full original complex Sobolev
preimage is retained at every order; no real-only hypothesis is imposed.
-/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- Original higher-action analyticity and physical trace data, retaining Section 23. -/
structure SourceSection24Data
    {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)
    {Wa : Set (CoeffPair 2)} (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s)
    (B U : Set (CoeffPair 2)) : Prop extends SourceSection23Data D A B U where
  higherAction_analytic : ∀ n : ℤ, ∀ k : ℕ,
    AnalyticOnNhd ℂ (sourceIndexedHigherAction (by simp) (by norm_num) n k) U
  sequence_analytic : ∀ r k : ℕ, k ≤ 2*r →
    AnalyticOnNhd ℂ (sourceIndexedHigherSobolevActionSequence r k)
      (higherSobolevSourceInclusion r ⁻¹' U)
  absolute_convergence : ∀ r k : ℕ, k ≤ 2*r → ∀ a : SobolevSource r,
    higherSobolevSourceInclusion r a ∈ U →
      Summable (fun n : ℤ => ‖sourceIndexedHigherAction (by simp) (by norm_num) n k
        (higherSobolevSourceInclusion r a)‖)
  trace : ∀ r k : ℕ, ∀ hk : k ≤ r, ∀ a : SobolevSource r,
    higherSobolevSourceInclusion r a ∈ U →
      (∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n k
        (higherSobolevSourceInclusion r a)) = sobolevNLSHamiltonian r a (k+1) (by omega)/2^k
  odd_trace : ∀ m : ℕ, ∀ hm : 1 ≤ m, ∀ a : SobolevSource m,
    higherSobolevSourceInclusion m a ∈ U →
      (∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n (2*m)
        (higherSobolevSourceInclusion m a)) = sobolevOddHamiltonian m hm a/4^m

/-- Add all original higher-action traces without changing the chosen family or source domain. -/
theorem SourceSection23Data.section24
    {W₀ W V Wa B U : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection23Data D A B U) : SourceSection24Data D A B U :=
  ⟨Q,Q.toSourceSection19Data.analytic_indexedHigherAction,
    Q.toSourceSection19Data.analytic_indexedHigherSobolevActionSequence,
    Q.toSourceSection19Data.summable_norm_indexedHigherAction,
    Q.toSourceSection19Data.indexedHigherAction_hamiltonian_trace,
    Q.toSourceSection19Data.indexedHigherAction_oddHamiltonian_trace⟩

/-- Theorem 24.1 with its printed level k and exact original H^(k−1) domain. -/
theorem SourceSection24Data.trace_printed_level
    {W₀ W V Wa B U : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection24Data D A B U) (k : ℕ) (hk : 1 ≤ k)
    (a : SobolevSource (k-1)) (ha : higherSobolevSourceInclusion (k-1) a ∈ U) :
    (∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n (k-1)
      (higherSobolevSourceInclusion (k-1) a)) =
        sobolevNLSHamiltonian (k-1) a k (by omega)/2^(k-1) := by
  simpa only [Nat.sub_add_cancel hk] using Q.trace (k-1) (k-1) le_rfl a ha

/-- The same retained Section 19 primitive supplies formula (5.2) at every level and index. -/
theorem SourceSection24Data.higherAction_eq_original_primitive
    {W₀ W V Wa B U : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection24Data D A B U) (ψ : CoeffPair 2) (hψ : ψ ∈ U)
    (n : ℤ) (k : ℕ) (q : ℤ)
    (C : SourceCriticalRootPeriodCircle (by simp) (by norm_num) ψ n) :
    sourceIndexedHigherAction (by simp) (by norm_num) n k ψ = -(Real.pi:ℂ)⁻¹ *
      ∮ z in C((C.center:ℂ),C.radius), z^k*sourceFullAbelianPrimitive (by simp) (by norm_num) B q (z,ψ) := by
  obtain ⟨E⟩ := Q.charts ψ hψ
  exact sourceIndexedHigherAction_eq_primitive C E k q

/-- Construct one original family before all levels and Sobolev orders. -/
theorem sourceSection24_original :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
      ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
      ∃ Wa : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
      ∃ B U : Set (CoeffPair 2), SourceSection24Data D A B U := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection23_original_estimates
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,Q.section24⟩
end NLS.ZakharovShabat
