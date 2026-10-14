import NLS.ZakharovShabat.SourceLemma10_1
import NLS.ZakharovShabat.SourceIsolatingMultiplicity

/-!
# The all-complex domain printed in Lemma 10.1 is impossible

For the smooth constant source (i*pi,i*pi), both raw frequencies +1 and
-1 carry square-zero two-dimensional operator blocks at spectral value
zero. Four independent generalized eigenvectors force multiplicity at
least four. Disjoint sets isolating each indexed periodic pair would force
multiplicity at most two, even without any disk or centering requirement.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The period-two Fourier coefficients of the constant potential (i*pi,i*pi). -/
def constantCollisionPotential : PairSpace p :=
  (lp.single p 0 (Complex.I*Real.pi),lp.single p 0 (Complex.I*Real.pi))

/-- First-row action of the actual constant potential operator. -/
theorem operator_collision_fst (hp : p ≠ ⊤) (f : Domain p) (n : ℤ) :
    (operator hp constantCollisionPotential f).1 n =
      -(Real.pi : ℂ)*n*f.1.val n+Complex.I*Real.pi*f.2.val n := by
  rw [operator_fst_apply]
  simp [constantCollisionPotential,lp.single_apply,Pi.single_apply,ite_mul,sub_eq_zero]

/-- Second-row action of the actual constant potential operator. -/
theorem operator_collision_snd (hp : p ≠ ⊤) (f : Domain p) (n : ℤ) :
    (operator hp constantCollisionPotential f).2 n =
      (Real.pi : ℂ)*n*f.2.val n+Complex.I*Real.pi*f.1.val n := by
  rw [operator_snd_apply]
  simp [constantCollisionPotential,lp.single_apply,Pi.single_apply,ite_mul,sub_eq_zero]

/-- Insert both component coefficients at one raw Fourier frequency. -/
def collisionModeEmbedding (k : ℤ) : (ℂ × ℂ) →L[ℂ] PairSpace p :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p k).prodMap
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p k)

/-- Literal coordinates of the one-frequency embedding. -/
@[simp] theorem collisionModeEmbedding_apply (k : ℤ) (a : ℂ × ℂ) :
    collisionModeEmbedding (p := p) k a = (lp.single p k a.1,lp.single p k a.2) := rfl

/-- The exact zero spectral pencil on a single Fourier block. -/
theorem collision_spectralPencil_mode (hp : p ≠ ⊤) (k : ℤ) (a b : ℂ) :
    spectralPencil hp constantCollisionPotential 0 (scalarMode k a,scalarMode k b) =
      domainInclusion (scalarMode k ((Real.pi : ℂ)*k*a-Complex.I*Real.pi*b),
        scalarMode k (-Complex.I*Real.pi*a-(Real.pi : ℂ)*k*b)) := by
  rw [spectralPencil_apply,zero_smul,zero_sub]
  apply Prod.ext <;> ext n
  · change -(operator hp constantCollisionPotential _).1 n = _
    rw [operator_collision_fst]
    by_cases hn : n = k <;> simp [hn]
    ring
  · change -(operator hp constantCollisionPotential _).2 n = _
    rw [operator_collision_snd]
    by_cases hn : n = k <;> simp [hn]
    ring

/-- At frequencies +1 or -1 the entire block lies in the second root space. -/
theorem collisionMode_mem_root_two (hp : p ≠ ⊤) (k : ℤ) (hk : k^2 = 1) (a : ℂ × ℂ) :
    collisionModeEmbedding (p := p) k a ∈ periodicRootSpace hp constantCollisionPotential 0 2 := by
  rw [mem_periodicRootSpace_succ]
  refine ⟨(scalarMode k a.1,scalarMode k a.2),by simp,?_⟩
  rw [collision_spectralPencil_mode,mem_periodicRootSpace_succ]
  refine ⟨_,rfl,?_⟩
  change spectralPencil hp constantCollisionPotential 0 _ = 0
  rw [collision_spectralPencil_mode]
  have hkC : (k : ℂ)^2 = 1 := by exact_mod_cast hk
  have hA : (Real.pi : ℂ)*k*((Real.pi : ℂ)*k*a.1-Complex.I*Real.pi*a.2)-
      Complex.I*Real.pi*(-Complex.I*Real.pi*a.1-(Real.pi : ℂ)*k*a.2) = 0 := by
    calc
      _ = (Real.pi : ℂ)^2*((k : ℂ)^2+Complex.I^2)*a.1 := by ring
      _ = 0 := by rw [hkC,Complex.I_sq]; ring
  have hB : -Complex.I*Real.pi*((Real.pi : ℂ)*k*a.1-Complex.I*Real.pi*a.2)-
      (Real.pi : ℂ)*k*(-Complex.I*Real.pi*a.1-(Real.pi : ℂ)*k*a.2) = 0 := by
    calc
      _ = (Real.pi : ℂ)^2*((k : ℂ)^2+Complex.I^2)*a.2 := by ring
      _ = 0 := by rw [hkC,Complex.I_sq]; ring
  rw [hA,hB]
  apply Prod.ext <;> ext n <;> simp

/-- Insert four independent coefficients into the two raw frequencies +1 and -1. -/
def collisionFourModeEmbedding : ((ℂ × ℂ) × (ℂ × ℂ)) →L[ℂ] PairSpace p :=
  (collisionModeEmbedding 1).comp (ContinuousLinearMap.fst ℂ _ _)+
    (collisionModeEmbedding (-1)).comp (ContinuousLinearMap.snd ℂ _ _)

/-- The four coordinates at the two distinct frequencies are independent. -/
theorem collisionFourModeEmbedding_injective :
    Function.Injective (collisionFourModeEmbedding (p := p)) := by
  intro a b h
  have h1 := congrArg (fun x : PairSpace p => x.1 1) h
  have h2 := congrArg (fun x : PairSpace p => x.2 1) h
  have h3 := congrArg (fun x : PairSpace p => x.1 (-1)) h
  have h4 := congrArg (fun x : PairSpace p => x.2 (-1)) h
  simp [collisionFourModeEmbedding,collisionModeEmbedding_apply] at h1 h2 h3 h4
  exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)

/-- The actual unbounded operator has algebraic multiplicity at least four at zero. -/
theorem four_le_collisionMultiplicity (hp : p ≠ ⊤) :
    4 ≤ periodicAlgebraicMultiplicity (p := p) hp constantCollisionPotential 0 := by
  let := finiteDimensional_periodicRootSpaceTop (p := p) hp constantCollisionPotential 0
  have hm (a : (ℂ × ℂ) × (ℂ × ℂ)) :
      collisionFourModeEmbedding a ∈ periodicRootSpaceTop (p := p) hp constantCollisionPotential 0 := by
    apply (mem_periodicRootSpaceTop hp constantCollisionPotential 0 _).mpr
    refine ⟨2,?_⟩
    exact (periodicRootSpace hp constantCollisionPotential 0 2).add_mem
      (collisionMode_mem_root_two hp 1 (by norm_num) a.1)
      (collisionMode_mem_root_two hp (-1) (by norm_num) a.2)
  let f := (collisionFourModeEmbedding (p := p)).toLinearMap.codRestrict _ hm
  have hf : Function.Injective f := by
    intro a b h
    exact collisionFourModeEmbedding_injective (congrArg Subtype.val h)
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  simpa [periodicAlgebraicMultiplicity] using hd

/-- The constant physical source with both components equal to i*pi. -/
def sourceCollisionPotential : CoeffPair p :=
  WithLp.toLp p (lp.single p 0 (Complex.I*Real.pi),lp.single p 0 (Complex.I*Real.pi))

/-- Period doubling preserves the zero Fourier mode exactly. -/
@[simp] theorem sourceCollisionPotential_periodOne :
    periodOnePotential (sourceCollisionPotential (p := p)) = constantCollisionPotential := by
  have hdouble (a : ℂ) : Coeff.periodDouble (lp.single p 0 a) = lp.single p 0 a := by
    ext k
    by_cases he : k % 2 = 0
    · obtain ⟨j,rfl⟩ : ∃ j : ℤ, k = 2*j := ⟨k/2,by omega⟩
      simp [lp.single_apply,Pi.single_apply]
    · have hk : k = 2*(k/2)+1 := by omega
      rw [hk,Coeff.periodDouble_odd]
      simp only [lp.single_apply,Pi.single_apply]
      rw [if_neg (by omega)]
  simp only [periodOnePotential_apply,sourceCollisionPotential,WithLp.toLp_fst,
    WithLp.toLp_snd,hdouble,constantCollisionPotential]

/-- The original source operator has the same multiplicity obstruction. -/
theorem four_le_sourceCollisionMultiplicity (hp : p ≠ ⊤) :
    4 ≤ periodicAlgebraicMultiplicity hp (periodOnePotential (sourceCollisionPotential (p := p))) 0 := by
  rw [sourceCollisionPotential_periodOne]
  exact four_le_collisionMultiplicity hp

/-- Disjoint sets containing each actual periodic pair allow multiplicity at most two. -/
theorem periodicMultiplicity_le_two_of_disjoint_clusters
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (D : ℤ → Set ℂ)
    (hcluster : ∀ n, sourceSpectralCluster hp hp1 ψ n ⊆ D n)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (z : ℂ) (hspec : z ∈ periodicSpectrum hp (periodOnePotential ψ)) :
    periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z ≤ 2 := by
  classical
  obtain ⟨n,hn⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) z).mp hspec
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let C := canonicalPeriodicCutoff hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let K := max C n.natAbs
  have hlabel := (canonicalPeriodicEndpoints_spec hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)).1
  have hcentral := hlabel.central_at_larger_cutoff K (le_max_left _ _)
  have hnK : n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    simp only [Finset.mem_Icc]
    have hnat : n.natAbs ≤ K := le_max_right C n.natAbs
    omega
  have hzD : z ∈ D n := by
    rcases hn with hL | hR
    · exact hL ▸ hcluster n (Or.inl rfl)
    · exact hR ▸ hcluster n (Or.inr (Or.inl rfl))
  have hzcentral : z ∈ centralPeriodicSpectrum hp (periodOnePotential ψ) K :=
    (hcentral.root_iff z).mp ⟨n,le_max_right C n.natAbs,
      by simpa only [eq_comm] using hn⟩
  have hzero (m : ℤ) (hmn : m ≠ n) : ({L m,R m} : Multiset ℂ).count z = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hz
    have hz' : z = L m ∨ z = R m := by
      simpa only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] using hz
    have hzM : z ∈ D m := by
      rcases hz' with hL | hR
      · rw [hL]; exact hcluster m (Or.inl rfl)
      · rw [hR]; exact hcluster m (Or.inr (Or.inl rfl))
    exact Set.disjoint_left.mp (hdisjoint n m hmn.symm) hzD hzM
  have hsum : (∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ({L m,R m} : Multiset ℂ).count z) =
      ({L n,R n} : Multiset ℂ).count z := by
    apply Finset.sum_eq_single n
    · intro m hm hmn
      exact hzero m hmn
    · intro hnot
      exact False.elim (hnot hnK)
  have hcount := hcentral.count_eq z
  rw [hsum,if_pos hzcentral] at hcount
  rw [← hcount]
  simpa using Multiset.count_le_card z ({L n,R n} : Multiset ℂ)

/-- This smooth constant source has no isolating family, even without restrictions on the shapes. -/
theorem sourceCollisionPotential_not_isolatable (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ¬ ∃ D : ℤ → Set ℂ,
      (∀ n, sourceSpectralCluster hp hp1 (sourceCollisionPotential (p := p)) n ⊆ D n) ∧
      (∀ i j, i ≠ j → Disjoint (D i) (D j)) := by
  rintro ⟨D,hcluster,hdisjoint⟩
  have hlo := four_le_sourceCollisionMultiplicity (p := p) hp
  have hspec := (periodicAlgebraicMultiplicity_pos_iff hp
    (periodOnePotential (sourceCollisionPotential (p := p))) 0).mp (by omega)
  have hhi := periodicMultiplicity_le_two_of_disjoint_clusters hp hp1
    sourceCollisionPotential D hcluster hdisjoint 0 hspec
  omega

/-- No neighborhood containing all complex original sources can have the property printed in Lemma 10.1. -/
theorem not_sourceLemma10_1_all_complex (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ¬ ∃ W : Set (CoeffPair p), Set.univ ⊆ W ∧
      ∀ ψ ∈ W, ∃ V : Set (CoeffPair p), ψ ∈ V ∧
        ∃ D c, SourceIsolatingNeighborhoods hp hp1 V D c := by
  rintro ⟨W,hW,h⟩
  obtain ⟨V,hV,D,c,hD⟩ := h sourceCollisionPotential (hW (mem_univ _))
  exact sourceCollisionPotential_not_isolatable hp hp1
    ⟨D,hD.cluster _ hV,hD.disjoint⟩

end NLS.ZakharovShabat
