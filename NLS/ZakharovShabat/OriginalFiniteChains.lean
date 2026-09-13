import NLS.ZakharovShabat.ClassicalFiniteChains

/-!
# Original finite parity chains and classical initial jets

The recursion keeps every vector in the original weighted domain. For prescribed
initial data, a finite chain exists exactly when every classical chain level
satisfies the parity endpoint condition; its top vector is unique.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- An original chain of length `n+1`, including its parity, domain, and all initial values. -/
def IsOriginalParityChain (φ : PairSpace 2) (z : ℂ) (r : ℤ) (v : ℕ → ℂ × ℂ) : ℕ → Domain 2 → Prop
  | 0,a => a ∈ domainParitySubspace r ∧ physicalDomain a 0 = v 0 ∧ spectralPencil (by simp) φ z a = 0
  | n+1,a => a ∈ domainParitySubspace r ∧ physicalDomain a 0 = v (n+1) ∧
      ∃ b : Domain 2, IsOriginalParityChain φ z r v n b ∧ spectralPencil (by simp) φ z a = domainInclusion b

/-- Only the specified finite initial segment is used by an original chain. -/
theorem IsOriginalParityChain.congr_initial {φ : PairSpace 2} {z : ℂ} {r : ℤ}
    {v w : ℕ → ℂ × ℂ} {n : ℕ} {a : Domain 2} (h : IsOriginalParityChain φ z r v n a)
    (hv : ∀ j ≤ n, v j = w j) : IsOriginalParityChain φ z r w n a := by
  induction n generalizing a with
  | zero => exact ⟨h.1,h.2.1.trans (hv 0 le_rfl),h.2.2⟩
  | succ n ih =>
    obtain ⟨ha,h0,b,hb,he⟩ := h
    exact ⟨ha,h0.trans (hv _ le_rfl),b,ih hb (fun j hj => hv j (hj.trans (Nat.le_succ n))),he⟩

/-- Every original chain has the required parity at its top. -/
theorem IsOriginalParityChain.parity {φ : PairSpace 2} {z : ℂ} {r : ℤ}
    {v : ℕ → ℂ × ℂ} {n : ℕ} {a : Domain 2} (h : IsOriginalParityChain φ z r v n a) :
    a ∈ domainParitySubspace r := by cases n <;> exact h.1

/-- Every original chain has the specified top initial vector. -/
theorem IsOriginalParityChain.initial {φ : PairSpace 2} {z : ℂ} {r : ℤ}
    {v : ℕ → ℂ × ℂ} {n : ℕ} {a : Domain 2} (h : IsOriginalParityChain φ z r v n a) :
    physicalDomain a 0 = v n := by cases n <;> exact h.2.1

/-- The explicit finite-chain recursion lies in the existing original root-space recursion. -/
theorem IsOriginalParityChain.mem_rootSpace {φ : PairSpace 2} {z : ℂ} {r : ℤ}
    {v : ℕ → ℂ × ℂ} {n : ℕ} {a : Domain 2} (h : IsOriginalParityChain φ z r v n a) :
    domainInclusion a ∈ periodicRootSpace (by simp) φ z (n+1) := by
  induction n generalizing a with
  | zero => exact (mem_periodicRootSpace_succ (by simp) φ z 0 _).mpr ⟨a,rfl,by simp [h.2.2]⟩
  | succ n ih =>
    obtain ⟨_,_,b,hb,he⟩ := h
    exact (mem_periodicRootSpace_succ (by simp) φ z (n+1) _).mpr ⟨a,rfl,he ▸ ih hb⟩

@[simp] theorem physicalDomainCurve_zero : physicalDomainCurve (0 : Domain 2) = 0 := by
  apply ContinuousMap.ext
  intro t
  simp [physicalDomainCurve,physicalDomain]

/-- The physical representative of an original chain is exactly the classical initial-jet curve. -/
theorem IsOriginalParityChain.physical_curve {φ : PairSpace 2} (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    {z : ℂ} {r : ℤ} {v : ℕ → ℂ × ℂ} {n : ℕ} {a : Domain 2}
    (h : IsOriginalParityChain φ z r v n a) : physicalDomainCurve a = classicalJetCurve Φ z v n := by
  induction n generalizing a with
  | zero =>
    have he : spectralPencil (by simp) φ z a = domainInclusion 0 := by simpa only [map_zero] using! h.2.2
    have hs := physicalDomain_eq_classicalForcedSolution φ Φ hΦ z a 0 he
    apply ContinuousMap.ext
    intro t
    change physicalDomain a t = _
    rw [hs t.property,h.2.1,physicalDomainCurve_zero,classicalForcedSolution_eq_curve_add_chain]
    simp
  | succ n ih =>
    obtain ⟨ha,h0,b,hb,he⟩ := h
    have hs := physicalDomain_eq_classicalForcedSolution φ Φ hΦ z a b he
    apply ContinuousMap.ext
    intro t
    change physicalDomain a t = _
    rw [hs t.property,h0,ih hb,classicalJetCurve_succ_apply]

/-- Fixed initial data at all finite levels determine the original top vector uniquely. -/
theorem IsOriginalParityChain.unique {φ : PairSpace 2} (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    {z : ℂ} {r : ℤ} {v : ℕ → ℂ × ℂ} {n : ℕ} {a b : Domain 2}
    (ha : IsOriginalParityChain φ z r v n a) (hb : IsOriginalParityChain φ z r v n b) : a = b := by
  apply physicalDomain_unit_injective_parity r a b ha.parity hb.parity
  intro t ht
  exact congrArg (fun g : Curve (ℂ × ℂ) => g ⟨t,ht⟩)
    ((ha.physical_curve Φ hΦ).trans (hb.physical_curve Φ hΦ).symm)

/-- All endpoint equations of a classical finite chain are necessary and sufficient for an original parity chain. -/
theorem exists_originalParityChain_iff_endpoints (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (v : ℕ → ℂ × ℂ) (n : ℕ) :
    (∃ a : Domain 2, IsOriginalParityChain φ z r v n a) ↔
      ∀ j ≤ n, classicalJetCurve Φ z v j ⟨1,by constructor <;> norm_num⟩ = wave r 1 • v j := by
  induction n with
  | zero =>
    constructor
    · rintro ⟨a,ha⟩ j hj
      have hj0 : j = 0 := by omega
      subst j
      have ht := physicalDomain_add_one_of_parity a r ha.parity 0
      have hc := congrArg (fun g : Curve (ℂ × ℂ) => g ⟨1,by constructor <;> norm_num⟩) (ha.physical_curve Φ hΦ)
      change physicalDomain a 1 = _ at hc
      simp only [zero_add] at ht
      simpa only [ha.initial] using hc.symm.trans ht
    · intro hend
      have he : classicalForcedSolution Φ z (physicalDomainCurve 0) (v 0) 1 = wave r 1 • v 0 := by
        rw [physicalDomainCurve_zero,classicalForcedSolution_eq_curve_add_chain Φ z 0 (v 0) ⟨1,by constructor <;> norm_num⟩]
        simpa using hend 0 le_rfl
      obtain ⟨a,ha,hp,h0⟩ := (exists_parity_preimage_iff_forced_endpoint φ hφ Φ hΦ z r 0
        (Submodule.zero_mem _) (v 0)).mpr he
      exact ⟨a,ha,h0,by simpa only [map_zero] using! hp⟩
  | succ n ih =>
    constructor
    · rintro ⟨a,ha,h0,b,hb,he⟩ j hj
      by_cases hjn : j ≤ n
      · exact ih.mp ⟨b,hb⟩ j hjn
      · have hj' : j = n+1 := by omega
        subst j
        have hchain : IsOriginalParityChain φ z r v (n+1) a := ⟨ha,h0,b,hb,he⟩
        have ht := physicalDomain_add_one_of_parity a r ha 0
        have hc := congrArg (fun g : Curve (ℂ × ℂ) => g ⟨1,by constructor <;> norm_num⟩)
          (hchain.physical_curve Φ hΦ)
        change physicalDomain a 1 = _ at hc
        simp only [zero_add] at ht
        simpa only [h0] using hc.symm.trans ht
    · intro hend
      obtain ⟨b,hb⟩ := ih.mpr (fun j hj => hend j (hj.trans (Nat.le_succ n)))
      have he : classicalForcedSolution Φ z (physicalDomainCurve b) (v (n+1)) 1 = wave r 1 • v (n+1) := by
        rw [hb.physical_curve Φ hΦ]
        exact (classicalJetCurve_succ_apply Φ z v n ⟨1,by constructor <;> norm_num⟩).symm.trans (hend (n+1) le_rfl)
      obtain ⟨a,ha,hp,h0⟩ := (exists_parity_preimage_iff_forced_endpoint φ hφ Φ hΦ z r b hb.parity (v (n+1))).mpr he
      exact ⟨a,ha,h0,b,hb,hp⟩

/-- Every vector of the original finite parity root space has a chain with some initial jet. -/
theorem mem_parity_rootSpace_iff_exists_initial_chain (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (z : ℂ) (r : ℤ) (n : ℕ) (a : Domain 2) :
    (domainInclusion a ∈ periodicRootSpace (by simp) φ z (n+1) ∧ a ∈ domainParitySubspace r) ↔
      ∃ v : ℕ → ℂ × ℂ, IsOriginalParityChain φ z r v n a := by
  constructor
  · intro h
    induction n generalizing a with
    | zero =>
      obtain ⟨f,hf,hp⟩ := (mem_periodicRootSpace_succ (by simp) φ z 0 _).mp h.1
      have hfa : f = a := domainInclusion_injective hf
      subst f
      exact ⟨fun _ => physicalDomain a 0,h.2,rfl,hp⟩
    | succ n ih =>
      obtain ⟨f,hf,hp⟩ := (mem_periodicRootSpace_succ (by simp) φ z (n+1) _).mp h.1
      have hfa : f = a := domainInclusion_injective hf
      subst f
      obtain ⟨b,hb,hpb⟩ := (mem_periodicRootSpace_succ (by simp) φ z n _).mp hp
      have hbr : b ∈ domainParitySubspace r := by
        apply (mem_domainParitySubspace r b).mpr
        rw [hb,← pairParityProjection_eq_self_iff,← spectralPencil_domainParityProjection (by simp) φ hφ,
          (domainParityProjection_eq_self_iff r a).mpr h.2]
      obtain ⟨v,hv⟩ := ih b ⟨(mem_periodicRootSpace_succ (by simp) φ z n _).mpr ⟨b,rfl,hpb⟩,hbr⟩
      refine ⟨Function.update v (n+1) (physicalDomain a 0),h.2,by simp,b,?_,hb.symm⟩
      exact hv.congr_initial (fun j hj => by rw [Function.update_of_ne (by omega)])
  · rintro ⟨v,h⟩
    exact ⟨h.mem_rootSpace,h.parity⟩

/-- The original top vector determines all the initial data in its finite chain. -/
theorem IsOriginalParityChain.initial_eq {φ : PairSpace 2} {z : ℂ} {r : ℤ}
    {v w : ℕ → ℂ × ℂ} {n : ℕ} {a : Domain 2}
    (hv : IsOriginalParityChain φ z r v n a) (hw : IsOriginalParityChain φ z r w n a) :
    ∀ j ≤ n, v j = w j := by
  induction n generalizing a with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact hv.initial.symm.trans hw.initial
  | succ n ih =>
    obtain ⟨_,hv0,b,hb,heb⟩ := hv
    obtain ⟨_,hw0,c,hc,hec⟩ := hw
    have hbc : b = c := domainInclusion_injective (heb.symm.trans hec)
    subst c
    intro j hj
    by_cases hjn : j ≤ n
    · exact ih hb hc j hjn
    · have hjs : j = n+1 := by omega
      subst j
      exact hv0.symm.trans hw0

end NLS.ZakharovShabat
