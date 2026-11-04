# Canonical critical labels and the actual earlier period-data basis

This step connects the actual rough Miura numerator to the Hilbert class used
by the already constructed period operator. It does not prove its periods on
the original contours and does not close a main article theorem.

## Exact free critical set

`FreeHillCriticalEnergies.lean` proves the actual free energy derivative at
zero is -1, the global squared-frequency derivative identity
`(2*z)*Delta_H'(z^2) = -2*sin z`, and the equivalence between a free critical
energy and membership in the positive sequence `freeHillEnergy j`. There is
no slit-plane restriction. In particular, zero is excluded as an energy
critical point. This uses the actual free trace, not an assumption about a
chosen Miura lift of the free potential.

## Labels and full complex germs

`hillHminusMiura_energyCritical_free` identifies every positive canonical
energy label at the free input. The complete free critical set and uniqueness
of strictly increasing enumerations determine the labels exactly.

`hillHminus_critical_branch_eq_canonical_of_real_path` compares any analytic
actual critical branch with that free value to the canonical branch, along
a real radial path inside a common domain. Both functions are complex
analytic at every point of the real path image. Analytic uniqueness on that
preconnected image propagates their initial full complex germ. Actual simple
root uniqueness then gives full complex germ equality at the endpoint.
This does not invoke an unproved identity principle from equality of values
on a real slice.

## Actual earlier basis

`hillHminusUniformNumerator_eq_canonical` identifies the filled scalar bases
at every energy once labels agree, by the exact moving divided difference
identity. The normalization is precisely `2*j*pi`, including at the critical
centers. `hillHminusNumeratorHilbert_eq_canonical` identifies the complete
Hilbert vectors, including their zero nonpositive coordinates.

`hillHminus_period_data_canonical_compatibility` applies to any verified
`HillHminusAllContourPeriodData` for the actual earlier critical family.
Given a real-preserving actual canonical chart through zero, one norm ball
is chosen before all real inputs, positive labels and energies. On that ball
all real inputs have the matching labels, full complex critical germs, and
identical entire Hilbert bases. The earlier data are retained: this lemma
applies to the period data used by the already constructed weighted inverse,
through its proved structure projection. The germ neighborhoods may depend
on the index; no uniform complex germ neighborhood across all indices is
asserted.

`hillHminus_period_data_actual_numerator_representation` places the actual
descended Miura numerator in the earlier period-data Hilbert basis, with the
genuine residue vector already constructed in `HillHminusOneMiuraResidueHilbert`.
One ball precedes all real inputs, all deleted coefficient families, all signed
numerator indices and all complex energies, including critical and central
values. Thus it applies in particular to the actually constructed normalized
NLS data. Representation and coefficient membership are proved, rather than
assumed as uniqueness hypotheses.

## Remaining obligations

Actual normalized NLS mapped energy loops still need comparison with the
original frequency-circle energy contours. This requires the appropriate
gap labels, root branch, shift and winding or homotopy argument, including
the finite head and collapsed gaps. The period inverse can identify the
coefficient vector with its normalized column only after those original
contour periods are proved. Weighted normalized-family identification,
coherent numerator charts, physical frequency(69), and all main theorem
obligations remain open.

Validation uses the prior full strict rebuild of the unchanged 415 modules,
strict compilation of these two new modules, and a new combined transitive
axiom audit of the enlarged 417-module selection. It is not a second full
rebuild of all 417 modules. Exact selections, source hashes, private fresh
outputs and seven provenance records are checked.
