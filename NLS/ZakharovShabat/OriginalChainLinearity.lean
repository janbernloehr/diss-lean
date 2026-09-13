import NLS.ZakharovShabat.OriginalBoundaryJets

/-!
# Linearity of original finite chains

Addition and complex scaling preserve the original parity, weighted domain,
pencil recursion, and physical initial data at every finite chain level.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
namespace NLS.ZakharovShabat

@[simp] theorem physicalDomain_add (a b : Domain 2) (t : ℝ) :
    physicalDomain (a+b) t = physicalDomain a t+physicalDomain b t := by
  apply Prod.ext
  · change sobolevSynthesis (by simp) (a.1+b.1) (t : AddCircle (2 : ℝ)) = _
    rw [map_add,ContinuousMap.add_apply]
    rfl
  · change sobolevSynthesis (by simp) (a.2+b.2) (t : AddCircle (2 : ℝ)) = _
    rw [map_add,ContinuousMap.add_apply]
    rfl

@[simp] theorem physicalDomain_smul (c : ℂ) (a : Domain 2) (t : ℝ) :
    physicalDomain (c • a) t = c • physicalDomain a t := by
  apply Prod.ext
  · change sobolevSynthesis (by simp) (c • a.1) (t : AddCircle (2 : ℝ)) = _
    rw [map_smul,ContinuousMap.smul_apply]
    rfl
  · change sobolevSynthesis (by simp) (c • a.2) (t : AddCircle (2 : ℝ)) = _
    rw [map_smul,ContinuousMap.smul_apply]
    rfl

/-- Adding original chains adds their initial data at every level. -/
theorem IsOriginalParityChain.add {φ : PairSpace 2} {z : ℂ} {r : ℤ}
    {v w : ℕ → ℂ × ℂ} {n : ℕ} {a b : Domain 2}
    (ha : IsOriginalParityChain φ z r v n a) (hb : IsOriginalParityChain φ z r w n b) :
    IsOriginalParityChain φ z r (v+w) n (a+b) := by
  induction n generalizing a b with
  | zero =>
    refine ⟨(domainParitySubspace r).add_mem ha.parity hb.parity,?_,?_⟩
    · rw [physicalDomain_add,ha.initial,hb.initial]
      rfl
    · rw [map_add,ha.2.2,hb.2.2,add_zero]
  | succ n ih =>
    obtain ⟨ha,ha0,a',ha',hea⟩ := ha
    obtain ⟨hb,hb0,b',hb',heb⟩ := hb
    refine ⟨(domainParitySubspace r).add_mem ha hb,?_,a'+b',ih ha' hb',?_⟩
    · rw [physicalDomain_add,ha0,hb0]
      rfl
    · rw [map_add,hea,heb,map_add]

/-- Complex scaling preserves each original source equation and scales the entire initial jet. -/
theorem IsOriginalParityChain.smul {φ : PairSpace 2} {z : ℂ} {r : ℤ}
    {v : ℕ → ℂ × ℂ} {n : ℕ} {a : Domain 2}
    (ha : IsOriginalParityChain φ z r v n a) (c : ℂ) :
    IsOriginalParityChain φ z r (c • v) n (c • a) := by
  induction n generalizing a with
  | zero =>
    refine ⟨(domainParitySubspace r).smul_mem c ha.parity,?_,?_⟩
    · rw [physicalDomain_smul,ha.initial]
      rfl
    · rw [map_smul,ha.2.2,smul_zero]
  | succ n ih =>
    obtain ⟨ha,ha0,b,hb,he⟩ := ha
    refine ⟨(domainParitySubspace r).smul_mem c ha,?_,c • b,ih hb,?_⟩
    · rw [physicalDomain_smul,ha0]
      rfl
    · rw [map_smul,he,map_smul]

/-- The alternating conversion of initial coefficients is additive. -/
@[simp] theorem signedInitialJet_add (v w : ℕ → ℂ × ℂ) :
    signedInitialJet (v+w) = signedInitialJet v+signedInitialJet w := by
  funext n
  exact smul_add _ _ _

/-- The alternating conversion of initial coefficients is complex linear. -/
@[simp] theorem signedInitialJet_smul (c : ℂ) (v : ℕ → ℂ × ℂ) :
    signedInitialJet (c • v) = c • signedInitialJet v := by
  funext n
  exact smul_comm ((-1 : ℂ)^n) c (v n)

end NLS.ZakharovShabat
