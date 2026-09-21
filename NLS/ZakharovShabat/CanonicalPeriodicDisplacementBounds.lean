import NLS.ZakharovShabat.SmallCompleteDisplacements
import NLS.ZakharovShabat.CanonicalPeriodicEndpoints
import NLS.SequenceSpaces.PairedTailBounds

/-!
# Uniform small tails of canonical periodic displacements

Ordering can exchange the two roots in a distant pair. Pairwise tail
bounds preserve the original small-tail estimates under these exchanges.
The fixed central box bounds the finitely many newly ordered coordinates.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full central multiset bounds every central endpoint displacement at a fixed cutoff. -/
theorem exists_bound_centralPeriodicLabel_displacements (hp : p ≠ ⊤) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (φ : PairSpace p) (ξ η : ℤ → ℂ), CentralPeriodicLabeling hp φ N ξ η →
      ∀ n : ℤ, n.natAbs ≤ N → ‖ξ n-(Real.pi : ℂ)*n‖ ≤ B ∧ ‖η n-(Real.pi : ℂ)*n‖ ≤ B := by
  obtain ⟨A,hA,hAb⟩ := (isBounded_centralSpectralBox N).exists_pos_norm_le
  let s := Finset.Icc (-(N : ℤ)) (N : ℤ)
  obtain ⟨D,hD,hDb⟩ := ((s.finite_toSet.image (fun n : ℤ => (Real.pi : ℂ)*n)).isBounded).exists_pos_norm_le
  refine ⟨A+D,by positivity,fun φ ξ η h n hn => ?_⟩
  have hns : n ∈ s := by simp only [s,Finset.mem_Icc]; omega
  have hx := (h.root_iff (ξ n)).mp ⟨n,hn,Or.inl rfl⟩
  have hy := (h.root_iff (η n)).mp ⟨n,hn,Or.inr rfl⟩
  have hfree := hDb ((Real.pi : ℂ)*n) ⟨n,hns,rfl⟩
  exact ⟨(norm_sub_le _ _).trans (add_le_add (hAb _ ((mem_centralPeriodicSpectrum hp φ N _).mp hx).2) hfree),
    (norm_sub_le _ _).trans (add_le_add (hAb _ ((mem_centralPeriodicSpectrum hp φ N _).mp hy).2) hfree)⟩

/-- Canonical displacements have bounded full norms and uniformly small tails near each potential. -/
theorem exists_uniform_small_canonicalPeriodicDisplacements (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U, ∀ hψ : ψ ∈ pairParitySubspace 0,
        ‖canonicalPeriodicLeftDisplacement hp hp1 ψ hψ‖ ≤ R ∧
        ‖canonicalPeriodicRightDisplacement hp hp1 ψ hψ‖ ≤ R ∧
        ∀ M : ℕ, N ≤ M →
          ‖canonicalPeriodicLeftDisplacement hp hp1 ψ hψ-
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M) (canonicalPeriodicLeftDisplacement hp hp1 ψ hψ)‖ ≤ ε ∧
          ‖canonicalPeriodicRightDisplacement hp hp1 ψ hψ-
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M) (canonicalPeriodicRightDisplacement hp hp1 ψ hψ)‖ ≤ ε := by
  obtain ⟨N,hN,V,ho,hconv,hφ,h0,_,_,hdata⟩ := exists_uniform_small_completeDisplacements hp hp1
    SpectralWeight.one (unitBaseEquiv.symm φ) (half_pos hε)
  have he (ψ : PairSpace p) : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm ψ) = ψ := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨B,hB,hbound⟩ := exists_bound_centralPeriodicLabel_displacements hp N
  let s := Finset.Icc (-(N : ℤ)) (N : ℤ)
  refine ⟨N,hN,unitBaseEquiv.symm ⁻¹' V,ho.preimage unitBaseEquiv.symm.continuous,
    hconv.linear_preimage (unitBaseEquiv.symm.toContinuousLinearMap.restrictScalars ℝ).toLinearMap,
    hφ,by simpa only [mem_preimage,map_zero] using h0,s.card*B+ε,by positivity,?_⟩
  intro ψ hψ heven
  obtain ⟨ξ,η,h,_,_,ht⟩ := hdata (unitBaseEquiv.symm ψ) hψ (by rw [he]; exact heven)
  have hE : PeriodicEndpointLabeling hp ψ N ξ η := by simpa only [he] using h.toEndpoints
  obtain ⟨α,β,hl,hw,hs,hpairs⟩ := hE.exists_ordered
  obtain ⟨hα,hβ⟩ := hl.eq_canonicalPeriodicEndpoints hp1 heven hw hs
  rw [hα,hβ] at hl hpairs
  let a : Coeff p := ⟨_,hE.left_displacement⟩
  let b : Coeff p := ⟨_,hE.right_displacement⟩
  let c := canonicalPeriodicLeftDisplacement hp hp1 ψ heven
  let d := canonicalPeriodicRightDisplacement hp hp1 ψ heven
  have hchoose (n : ℤ) (hn : N < n.natAbs) :
      (c n = a n ∨ c n = b n) ∧ (d n = a n ∨ d n = b n) := by
    have hx : canonicalPeriodicLeft hp hp1 ψ heven n ∈
        ({canonicalPeriodicLeft hp hp1 ψ heven n,canonicalPeriodicRight hp hp1 ψ heven n} : Multiset ℂ) := by simp
    have hy : canonicalPeriodicRight hp hp1 ψ heven n ∈
        ({canonicalPeriodicLeft hp hp1 ψ heven n,canonicalPeriodicRight hp hp1 ψ heven n} : Multiset ℂ) := by simp
    rw [hpairs n hn] at hx hy
    have hx' : canonicalPeriodicLeft hp hp1 ψ heven n = ξ n ∨ canonicalPeriodicLeft hp hp1 ψ heven n = η n := by simpa using hx
    have hy' : canonicalPeriodicRight hp hp1 ψ heven n = ξ n ∨ canonicalPeriodicRight hp hp1 ψ heven n = η n := by simpa using hy
    constructor
    · rcases hx' with hx' | hx' <;>
        simp only [c,canonicalPeriodicLeftDisplacement_apply,hx',a,b] <;> simp
    · rcases hy' with hy' | hy' <;>
        simp only [d,canonicalPeriodicRightDisplacement_apply,hy',a,b] <;> simp
  have htail (M : ℕ) (hM : N ≤ M) :
      ‖c-Coeff.truncate (Finset.Icc (-(M : ℤ)) M) c‖ ≤ ε ∧
      ‖d-Coeff.truncate (Finset.Icc (-(M : ℤ)) M) d‖ ≤ ε := by
    have hab : ‖a-Coeff.truncate (Finset.Icc (-(M : ℤ)) M) a‖ ≤ ε/2 ∧
        ‖b-Coeff.truncate (Finset.Icc (-(M : ℤ)) M) b‖ ≤ ε/2 := ht M hM
    have hfar (n : ℤ) (hn : n ∉ Finset.Icc (-(M : ℤ)) M) : N < n.natAbs := by
      simp only [Finset.mem_Icc] at hn
      omega
    constructor
    · exact (Coeff.norm_sub_truncate_le_of_mem_pair a b c _ (fun n hn => (hchoose n (hfar n hn)).1)).trans
        (by linarith [hab.1,hab.2])
    · exact (Coeff.norm_sub_truncate_le_of_mem_pair a b d _ (fun n hn => (hchoose n (hfar n hn)).2)).trans
        (by linarith [hab.1,hab.2])
  have hcentral (n : ℤ) (hn : n ∈ s) : ‖c n‖ ≤ B ∧ ‖d n‖ ≤ B :=
    hbound ψ _ _ hl.central n (by simp only [s,Finset.mem_Icc] at hn; omega)
  refine ⟨?_,?_,htail⟩
  · exact (Coeff.norm_le_of_eq_outside_finset c (c-Coeff.truncate s c) s B
      (fun n hn => (hcentral n hn).1) (fun n hn => by simp [Coeff.truncate_apply,hn])).trans
        (add_le_add le_rfl (htail N le_rfl).1)
  · exact (Coeff.norm_le_of_eq_outside_finset d (d-Coeff.truncate s d) s B
      (fun n hn => (hcentral n hn).2) (fun n hn => by simp [Coeff.truncate_apply,hn])).trans
        (add_le_add le_rfl (htail N le_rfl).2)

/-- Canonical endpoint displacement norms are bounded on a common open convex neighborhood. -/
theorem exists_uniform_bounded_canonicalPeriodicDisplacements (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ R : ℝ, 0 ≤ R ∧
      ∀ ψ ∈ U, ∀ hψ : ψ ∈ pairParitySubspace 0,
        ‖canonicalPeriodicLeftDisplacement hp hp1 ψ hψ‖ ≤ R ∧
        ‖canonicalPeriodicRightDisplacement hp hp1 ψ hψ‖ ≤ R := by
  obtain ⟨_,_,U,ho,hc,hφ,h0,R,hR,h⟩ := exists_uniform_small_canonicalPeriodicDisplacements hp hp1 φ
    (by norm_num : (0 : ℝ) < 1)
  exact ⟨U,ho,hc,hφ,h0,R,hR,fun ψ hψ heven => ⟨(h ψ hψ heven).1,(h ψ hψ heven).2.1⟩⟩

end NLS.ZakharovShabat
