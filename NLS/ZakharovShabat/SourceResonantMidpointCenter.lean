import NLS.ZakharovShabat.WeightedResonantMidpointCenter
import NLS.ZakharovShabat.ResonantOffDiagonalMajorants
import NLS.ZakharovShabat.SourcePeriodicMidpointAsymptotics
import NLS.ZakharovShabat.SourceWeightedPeriodOne

/-!
# Midpoint-center estimates in the original source variables

Common source neighborhoods supply actual counted pairs, identify their
midpoints with the canonical endpoint average, and control the complete
off-diagonal product by two bounded ℓp coefficient sequences.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem midpoint_pullback {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A → B) (he : Continuous e) (a : A) (P : ℕ → B → Prop)
    (h : ∃ N : ℕ, ∃ U : Set B, IsOpen U ∧ e a ∈ U ∧ ∀ x ∈ U, P N x) :
    ∃ N : ℕ, ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, P N (e x) := by
  obtain ⟨N,U,ho,ha,hP⟩ := h
  exact ⟨N,e ⁻¹' U,ho.preimage he,ha,fun x hx => hP (e x) hx⟩

/-- Canonical endpoint pairs on the physical weighted space at a common cutoff. -/
theorem exists_uniform_weightedCanonicalEndpointPairs (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, ∃ U : Set (WeightedCoeffPair w.toWeight p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ hψ : weightedBaseToPair w ψ ∈ pairParitySubspace 0,
        ∀ n : ℤ, N ≤ n.natAbs → PeriodicEndpointPair hp (weightedBaseToPair w ψ) n
          (canonicalPeriodicLeft hp hp1 _ hψ n) (canonicalPeriodicRight hp hp1 _ hψ n) := by
  obtain ⟨N,_,U,ho,_,hφ,_,h⟩ := exists_uniform_canonicalPeriodicEndpoints hp hp1 w φ
  exact ⟨N+1,U,ho,hφ,fun ψ hψ heven n hn => (h ψ hψ heven N le_rfl).distant n (by omega)⟩

/-- Canonical endpoint pairs are valid on one original-source neighborhood. -/
theorem exists_uniform_sourceCanonicalEndpointPairs (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, N ≤ n.natAbs → PeriodicEndpointPair hp (periodOnePotential ψ) n
        (canonicalPeriodicLeft hp hp1 _ (periodOnePotential_mem ψ) n)
        (canonicalPeriodicRight hp hp1 _ (periodOnePotential_mem ψ) n) := by
  obtain ⟨N,V,ho,hφ,h⟩ := midpoint_pullback sourceWeightedPeriodOne
    sourceWeightedPeriodOne.toContinuousLinearMap.continuous φ _
    (exists_uniform_weightedCanonicalEndpointPairs hp hp1 SpectralWeight.one (sourceWeightedPeriodOne φ))
  refine ⟨N,V,ho,hφ,?_⟩
  intro ψ hψ n hn
  have hh := h ψ hψ
  rw [weightedBaseToPair_sourceWeightedPeriodOne] at hh
  exact hh (periodOnePotential_mem ψ) n hn

/-- Counted resonant pairs and canonical pairs have the same midpoint. -/
theorem PeriodicResonantPair.midpoint_eq_endpointPair {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {n : ℤ} {x y u v : ℂ}
    (h : PeriodicResonantPair hp w φ n x y)
    (k : PeriodicEndpointPair hp (weightedBaseToPair w φ) n u v) : (x+y)/2 = (u+v)/2 := by
  have hk := enclosedPeriodicSpectrum_eq_rootPair hp _ n u v k.left_mem k.right_mem k.spectrum_iff
  have he := congrArg (fun s : Finset ℂ => (s:Set ℂ)) (h.enclosed_eq.symm.trans hk)
  rcases Set.pair_eq_pair_iff.mp (by simpa only [Finset.coe_insert,Finset.coe_singleton] using he) with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · rw [add_comm]

/-- The canonical original-source midpoint obeys the product estimate on one neighborhood. -/
theorem exists_uniform_sourceMidpointCenterBound (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, N ≤ n.natAbs →
        ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
          weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n‖ ≤
            (8*Real.pi⁻¹)*resonantBProductSup hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n := by
  have hw := exists_uniform_weightedMidpointCenterBound hp hp1 SpectralWeight.one (sourceWeightedPeriodOne φ)
  obtain ⟨N,hN,U,ho,hφ,h⟩ := hw
  have hw' := midpoint_pullback sourceWeightedPeriodOne sourceWeightedPeriodOne.toContinuousLinearMap.continuous
    φ (fun K ψ => ∀ n : ℤ, K ≤ n.natAbs →
      ∃ x y : ℂ, PeriodicResonantPair hp SpectralWeight.one ψ n x y ∧
        ‖(x+y)/2-weightedResonantDiagonalCenter hp SpectralWeight.one ψ n‖ ≤
          (8*Real.pi⁻¹)*resonantBProductSup hp SpectralWeight.one ψ n) ⟨N,U,ho,hφ,h⟩
  obtain ⟨N₁,V₁,ho₁,hφ₁,h₁⟩ := hw'
  obtain ⟨N₂,V₂,ho₂,hφ₂,h₂⟩ := exists_uniform_sourceCanonicalEndpointPairs hp hp1 φ
  refine ⟨max N₁ N₂,V₁ ∩ V₂,ho₁.inter ho₂,⟨hφ₁,hφ₂⟩,?_⟩
  intro ψ hψ n hn
  obtain ⟨x,y,hpair,hb⟩ := h₁ ψ hψ.1 n (by omega)
  have hk := h₂ ψ hψ.2 n (by omega)
  have hk' : PeriodicEndpointPair hp (weightedBaseToPair SpectralWeight.one (sourceWeightedPeriodOne ψ)) n
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) := by
    rwa [weightedBaseToPair_sourceWeightedPeriodOne]
  rw [hpair.midpoint_eq_endpointPair hk'] at hb
  exact hb

/-- The actual unit-weight off-diagonal remainder estimates, with no inverse witness retained. -/
theorem exists_uniform_unitOffDiagonalRemainderBounds (hp : p ≠ ⊤)
    (φ : WeightedCoeffPair SpectralWeight.one.toWeight p) :
    ∃ N : ℕ, ∃ U : Set (WeightedCoeffPair SpectralWeight.one.toWeight p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
        ‖weightedResonantBMinusExtension hp SpectralWeight.one ψ n z-ψ.fst.val (-(2*n))‖ ≤
          resonantBMinusRemainderBound hp SpectralWeight.one ψ n ∧
        ‖weightedResonantBPlusExtension hp SpectralWeight.one ψ n z-ψ.snd.val (2*n)‖ ≤
          resonantBPlusRemainderBound hp SpectralWeight.one ψ n := by
  obtain ⟨N,_,U,ho,_,hφ,_,h⟩ := exists_uniform_offDiagonalHolder hp SpectralWeight.one φ
  refine ⟨N,U,ho,hφ,?_⟩
  intro ψ hψ n hn z hz
  obtain ⟨_,_,_,hm,hp'⟩ := h ψ hψ n hn z hz
  simpa only [SpectralWeight.one_apply,one_mul] using And.intro hm hp'

/-- Two bounded ℓp majorants control the actual source product suprema on every distant strip. -/
theorem exists_uniform_sourceBProductMajorants (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ ψ ∈ V, ∃ B C : Coeff p, ‖B‖ ≤ L ∧ ‖C‖ ≤ L ∧
        ∀ n : ℤ, N ≤ n.natAbs → resonantBProductSup hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ≤
          ‖B n‖*‖C n‖ := by
  obtain ⟨N,V,ho,hφ,h⟩ := midpoint_pullback sourceWeightedPeriodOne
    sourceWeightedPeriodOne.toContinuousLinearMap.continuous φ _
    (exists_uniform_unitOffDiagonalRemainderBounds hp (sourceWeightedPeriodOne φ))
  let R := ‖φ‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨N,V ∩ ball φ 1,ho.inter isOpen_ball,⟨hφ,mem_ball_self (by norm_num)⟩,
    resonantOffDiagonalNormBudget hp hp1 R,resonantOffDiagonalNormBudget_nonneg hp hp1 hR,?_⟩
  intro ψ hψ
  have hn : ‖sourceWeightedPeriodOne ψ‖ ≤ R := by
    rw [norm_sourceWeightedPeriodOne]
    have hb := mem_ball.mp hψ.2
    rw [dist_eq_norm] at hb
    have ht := norm_le_norm_sub_add ψ φ
    dsimp [R]
    linarith
  obtain ⟨B,C,hB,hC,_,hBC⟩ := exists_unitOffDiagonalMajorants hp hp1 (sourceWeightedPeriodOne ψ) N hn (h ψ hψ.1)
  exact ⟨B,C,hB,hC,hBC⟩

end NLS.ZakharovShabat
