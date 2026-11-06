import NLS.ZakharovShabat.SourceComponentSwapSpectralData
import NLS.ZakharovShabat.CanonicalPeriodicEndpoints
import NLS.SequenceSpaces.Reflection

/-! # Exact signed periodic endpoint labels under component swap

Complete ordered labels, the original central root multiplicities, distant
spectral discs and lp displacements fix the reflection n -> -n. The left
and right endpoint slots exchange. No simple-root or real-type restriction
is needed for this label identity.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem complexLexLE_neg_reverse {x y : ℂ} (h : complexLexLE x y) :
    complexLexLE (-y) (-x) := by
  rcases (complexLexLE_iff x y).mp h with h | ⟨he,h⟩
  · apply complexLexLE_of_re_lt
    simpa only [neg_re,neg_lt_neg_iff] using h
  · apply (complexLexLE_iff _ _).mpr
    right
    exact ⟨by simpa only [neg_re] using congrArg Neg.neg he.symm,
      by simpa only [neg_im,neg_le_neg_iff] using h⟩

private theorem sum_symmetricInterval_neg {M : Type*} [AddCommMonoid M]
    (N : ℕ) (f : ℤ → M) :
    (∑ n ∈ Finset.Icc (-(N:ℤ)) N, f (-n)) = ∑ n ∈ Finset.Icc (-(N:ℤ)) N, f n := by
  apply Finset.sum_bij (fun n _ => -n)
  · intro n hn
    simp only [Finset.mem_Icc] at *
    omega
  · intro n _ m _ h
    exact neg_injective h
  · intro n hn
    refine ⟨-n,?_,neg_neg n⟩
    simp only [Finset.mem_Icc] at *
    omega
  · intro n _
    rfl

private theorem count_neg_pair (x y z : ℂ) :
    ({-y,-x} : Multiset ℂ).count z = ({x,y} : Multiset ℂ).count (-z) := by
  classical
  have hx : z = -x ↔ x = -z := by
    constructor <;> intro h <;> simpa only [neg_neg] using congrArg Neg.neg h.symm
  have hy : z = -y ↔ y = -z := by
    constructor <;> intro h <;> simpa only [neg_neg] using congrArg Neg.neg h.symm
  simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton]
  simp only [eq_comm,hx,hy]
  omega

/-- Negation reflects the original quarter-pi disc with its signed label. -/
theorem neg_mem_refinedResonantDisk_iff (n : ℤ) (z : ℂ) :
    -z ∈ refinedResonantDisk (-n) ↔ z ∈ refinedResonantDisk n := by
  simp only [refinedResonantDisk,mem_ball,dist_eq_norm,Int.cast_neg,mul_neg]
  have he : -z- -((Real.pi:ℂ)*n) = -(z-(Real.pi:ℂ)*n) := by ring
  rw [he,norm_neg]

/-- Negation reflects the full distant strip, retaining its boundary. -/
theorem neg_mem_resonantStrip_iff (n : ℤ) (z : ℂ) :
    -z ∈ resonantStrip (-n) ↔ z ∈ resonantStrip n := by
  simp only [resonantStrip,Set.mem_ofPred_eq,neg_re,Int.cast_neg,mul_neg]
  have he : -z.re- -(Real.pi*n) = -(z.re-Real.pi*n) := by ring
  rw [he,abs_neg]

/-- The original counted distant pair reflects and exchanges its two slots. -/
theorem componentSwap_periodicEndpointPair (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (x y : ℂ)
    (h : PeriodicEndpointPair hp (periodOnePotential φ) n x y) :
    PeriodicEndpointPair hp (periodOnePotential (sourceComponentSwap φ)) (-n) (-y) (-x) := by
  refine ⟨(neg_mem_refinedResonantDisk_iff n y).mpr h.right_mem,
    (neg_mem_refinedResonantDisk_iff n x).mpr h.left_mem,?_,?_⟩
  · intro z hz
    have hstrip : -z ∈ resonantStrip n := by
      simpa only [neg_neg] using (neg_mem_resonantStrip_iff (-n) z).mpr hz
    have hs : z ∈ periodicSpectrum hp (periodOnePotential (sourceComponentSwap φ)) ↔
        -z ∈ periodicSpectrum hp (periodOnePotential φ) := by
      simpa only [neg_neg] using sourcePeriodicSpectrum_componentSwap hp hp1 φ (-z)
    simpa only [neg_eq_iff_eq_neg,or_comm] using hs.trans (h.spectrum_iff (-z) hstrip)
  · intro z hz
    have hstrip : -z ∈ resonantStrip n := by
      simpa only [neg_neg] using (neg_mem_resonantStrip_iff (-n) z).mpr hz
    have hm := sourcePeriodicMultiplicity_componentSwap hp hp1 φ (-z)
    rw [neg_neg,h.multiplicity_eq_count (-z) hstrip] at hm
    exact hm.trans (count_neg_pair x y z).symm

/-- The canonical periodic endpoint labels transform with exactly n -> -n,
exchanging left and right even through all endpoint collisions. -/
theorem sourceCanonicalPeriodicEndpoints_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceComponentSwap φ)) (periodOnePotential_mem _) n =
      -canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential (sourceComponentSwap φ)) (periodOnePotential_mem _) n =
      -canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n) := by
  classical
  let ξ := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _)
  let η := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _)
  let α := fun k : ℤ => -η (-k)
  let β := fun k : ℤ => -ξ (-k)
  have ho := canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem _)
  obtain ⟨N₀,U,_,_,_,hU,_,_,_,hcount⟩ :=
    exists_uniform_periodicCountingData hp (periodOnePotential (sourceComponentSwap φ))
  let N := max N₀ (canonicalPeriodicCutoff hp hp1 (periodOnePotential φ) (periodOnePotential_mem _))
  have hN₀ : N₀ ≤ N := le_max_left _ _
  have hN : canonicalPeriodicCutoff hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) ≤ N := le_max_right _ _
  have hc := ho.1.central_at_larger_cutoff N hN
  have ha : Memℓp (fun k : ℤ => α k-(Real.pi:ℂ)*k) p := by
    let a : Coeff p := ⟨fun k => η k-(Real.pi:ℂ)*k,ho.1.right_displacement⟩
    have he : (fun k : ℤ => α k-(Real.pi:ℂ)*k) = fun k => (-Coeff.reflection a) k := by
      funext k
      change -η (-k)-(Real.pi:ℂ)*k = -(η (-k)-(Real.pi:ℂ)*((-k:ℤ):ℂ))
      push_cast
      ring
    rw [he]
    exact lp.memℓp _
  have hb : Memℓp (fun k : ℤ => β k-(Real.pi:ℂ)*k) p := by
    let b : Coeff p := ⟨fun k => ξ k-(Real.pi:ℂ)*k,ho.1.left_displacement⟩
    have he : (fun k : ℤ => β k-(Real.pi:ℂ)*k) = fun k => (-Coeff.reflection b) k := by
      funext k
      change -ξ (-k)-(Real.pi:ℂ)*k = -(ξ (-k)-(Real.pi:ℂ)*((-k:ℤ):ℂ))
      push_cast
      ring
    rw [he]
    exact lp.memℓp _
  have hcentral : CentralPeriodicLabeling hp (periodOnePotential (sourceComponentSwap φ)) N α β := by
    constructor
    apply Multiset.ext.mpr
    intro z
    rw [Multiset.count_sum']
    calc
      (∑ k ∈ Finset.Icc (-(N:ℤ)) N, ({α k,β k} : Multiset ℂ).count z) =
          ∑ k ∈ Finset.Icc (-(N:ℤ)) N, ({ξ (-k),η (-k)} : Multiset ℂ).count (-z) := by
        apply Finset.sum_congr rfl
        intro k _
        exact count_neg_pair (ξ (-k)) (η (-k)) z
      _ = ∑ k ∈ Finset.Icc (-(N:ℤ)) N, ({ξ k,η k} : Multiset ℂ).count (-z) :=
        sum_symmetricInterval_neg N (fun k : ℤ => ({ξ k,η k} : Multiset ℂ).count (-z))
      _ = (centralPeriodicRoots hp (periodOnePotential φ) N).count (-z) := by
        rw [← Multiset.count_sum',hc.roots]
      _ = (centralPeriodicRoots hp (periodOnePotential (sourceComponentSwap φ)) N).count z := by
        simpa only [neg_neg] using (sourceCentralPeriodicRoots_count_componentSwap hp hp1 φ N (-z)).symm
  have hlabel : PeriodicEndpointLabeling hp (periodOnePotential (sourceComponentSwap φ)) N α β := by
    refine ⟨hcount _ hU N hN₀,hcentral,?_,ha,hb⟩
    intro k hk
    have hpast : canonicalPeriodicCutoff hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) < (-k).natAbs := by
      simpa only [Int.natAbs_neg] using lt_of_le_of_lt hN hk
    exact (by simpa only [neg_neg] using componentSwap_periodicEndpointPair hp hp1 φ (-k) (ξ (-k)) (η (-k)) (ho.1.distant (-k) hpast))
  have hw (k : ℤ) : complexLexLE (α k) (β k) := complexLexLE_neg_reverse (ho.2.1 (-k))
  have hcross (i j : ℤ) (hij : i < j) : complexLexLE (β i) (α j) :=
    complexLexLE_neg_reverse (ho.2.2 (-j) (-i) (neg_lt_neg hij))
  obtain ⟨hl,hr⟩ := hlabel.eq_canonicalPeriodicEndpoints hp1 (periodOnePotential_mem _) hw hcross
  exact ⟨(congrFun hl n).symm,(congrFun hr n).symm⟩

end NLS.ZakharovShabat
