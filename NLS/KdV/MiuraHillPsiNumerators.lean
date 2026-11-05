import NLS.KdV.MiuraCanonicalRootReflection
import NLS.KdV.MiuraCanonicalEndpoints
import NLS.ZakharovShabat.SourcePsiReflectionPeriods

/-! Actual jointly analytic energy numerators on one common complex Miura
source neighborhood. The factory uses the verified simultaneous Dirac psi
construction, and every positive-index pullback period has the exact Hill
normalization. Independence from the Miura representation is a further step. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

/-- One verified simultaneous original psi family, retaining its actual root maps. -/
structure MiuraHillPsiFamily where
  originalDomain : Set (CoeffPair 2)
  original_open : IsOpen originalDomain
  original_connected : IsConnected originalDomain
  original_real_subset : realTypeSourceLocus 2 ⊆ originalDomain
  domain : Set (CoeffPair 2)
  domain_open : IsOpen domain
  domain_simplyConnected : IsSimplyConnected domain
  real_subset : realTypeSourceLocus 2 ⊆ domain
  roots : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n
  verified : SourceTheorem12_1Data (by norm_num) (by norm_num) originalDomain domain roots

/-- The family is constructed from proved results, without supplied period hypotheses. -/
theorem nonempty_miuraHillPsiFamily : Nonempty MiuraHillPsiFamily := by
  obtain ⟨W₀,hW₀,hC₀,hR₀,W,hW,hC,hR,s,H⟩ := sourceTheorem12_1 (p := 2) (by norm_num) (by norm_num)
  exact ⟨⟨W₀,hW₀,hC₀,hR₀,W,hW,hC,hR,s,H⟩⟩

namespace MiuraHillPsiFamily

def source (B : MiuraHillPsiFamily) : Set (Coeff 2) := hillMiuraDiagonal ⁻¹' B.domain

theorem source_open (B : MiuraHillPsiFamily) : IsOpen B.source :=
  B.domain_open.preimage hillMiuraDiagonal.continuous

theorem real_mem_source (B : MiuraHillPsiFamily) (u : PeriodOneRealL2) : u.val ∈ B.source :=
  B.real_subset (isRealType_hillMiuraDiagonal u)

/-- The actual all-index energy numerator on this common complex source domain. -/
def numerator (B : MiuraHillPsiFamily) (n : ℕ+) (t : ℂ × Coeff 2) : ℂ :=
  sourcePsiEnergyNumerator B.roots ((n:ℕ):ℤ) (t.1,hillMiuraDiagonal t.2)

theorem analytic_numerator (B : MiuraHillPsiFamily) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.numerator n) (univ ×ˢ B.source) := by
  intro t ht
  have hd : AnalyticAt ℂ (fun x : ℂ × Coeff 2 => hillMiuraDiagonal x.2) t :=
    (hillMiuraDiagonal.analyticAt t.2).comp (f := Prod.snd) analyticAt_snd
  exact (B.verified.analytic_energyNumerator B.domain_open ((n:ℕ):ℤ)
    (t.1,hillMiuraDiagonal t.2) ⟨mem_univ _,ht.2⟩).comp
      (f := fun x : ℂ × Coeff 2 => (x.1,hillMiuraDiagonal x.2)) (analyticAt_fst.prod hd)

/-- The exact quadratic pullback numerator, including zero frequency. -/
theorem numerator_frequency_identity (B : MiuraHillPsiFamily) (n : ℕ+) (u : Coeff 2) (z : ℂ) :
    2*z*B.numerator n (z^2,u) =
      sourcePsiCandidate ((n:ℕ):ℤ) (z,(B.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u):Coeff 2))-
      sourcePsiCandidate ((n:ℕ):ℤ) (-z,(B.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u):Coeff 2)) :=
  two_mul_frequency_oddSquareDescent
    (sourceSelectedPsiNumerator B.roots ((n:ℕ):ℤ)) (hillMiuraDiagonal u) z

/-- Every positive-index period has the actual Kronecker value and literal 1/(2π). -/
theorem numerator_pullback_period (B : MiuraHillPsiFamily) (n m : ℕ+) (u : Coeff 2)
    (hu : u ∈ B.source)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u) ((m:ℕ):ℤ)) :
    (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
      (2*z*B.numerator n (z^2,u))/
        sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u) z) =
      if m = n then 1 else 0 := by
  have h := B.verified.energyNumerator_pullback_period (hillMiuraDiagonal u) hu
    (sourcePeriodicReflection_hillMiuraDiagonal u) ((n:ℕ):ℤ) ((m:ℕ):ℤ) D
  have hn : 0 < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
  have hm : 0 < ((m:ℕ):ℤ) := by exact_mod_cast m.pos
  have hneg : -((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by omega
  have he : ((m:ℕ):ℤ) = ((n:ℕ):ℤ) ↔ m = n := by
    constructor
    · intro hmn
      apply Subtype.ext
      exact Int.ofNat.inj hmn
    · intro hmn
      rw [hmn]
  rw [if_neg hneg,sub_zero] at h
  simpa only [numerator,he] using h

/-- The normalized period assertions use actual nonempty original circle families. -/
theorem nonempty_periodCircle (B : MiuraHillPsiFamily) (u : Coeff 2) (hu : u ∈ B.source) (m : ℕ+) :
    Nonempty (SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u) ((m:ℕ):ℤ)) :=
  B.verified.nonempty_periodCircle (hillMiuraDiagonal u) hu ((m:ℕ):ℤ)

/-- Every fixed physical energy shift preserves joint analyticity of this family. -/
theorem analytic_shifted_numerator (B : MiuraHillPsiFamily) (n : ℕ+) (c : ℂ) :
    AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => B.numerator n (t.1+c,t.2)) (univ ×ˢ B.source) := by
  intro t ht
  exact (B.analytic_numerator n (t.1+c,t.2) ⟨mem_univ _,ht.2⟩).comp
    (f := fun x : ℂ × Coeff 2 => (x.1+c,x.2))
    ((analyticAt_fst.add analyticAt_const).prod analyticAt_snd)

end MiuraHillPsiFamily
end NLS.KdV
