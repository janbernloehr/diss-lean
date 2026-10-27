# Reviewed numbered headings

The [generated candidate inventory](statement-candidates.json) indexes 156
labels from the dissertation extraction. Manual review distinguishes 152
actual theorem, lemma, proposition or corollary headings from four labels
that occur only in references. The extraction also contains nine numbered
remark headings, which the candidate generator intentionally does not match.

The [reviewed location index](reviewed-headings.json) records these 161
headings, source positions and links to their focused audits. This is a
navigation review. It does not certify that 161 mathematical statements are
proved, or account for every unnumbered assertion, displayed formula and
proof sentence. The focused audits record the implemented domains,
corrections and remaining qualifications; a heading match is not a proof.

The [source-comparison snapshot](source-review-index.json) now publishes the
recorded comparisons for these headings, together with selected unnumbered
assertions, declaration references, review qualifications, and module hashes.
It contains 46 review records and 609 module-hash entries covering 577 distinct
modules. The exact 2014 reference comparison and Appendix G.2 interval-norm
interpretation remain unresolved. No completeness percentage is inferred.

From the repository root, check the snapshot with:

```sh
python3 scripts/check_source_reviews.py
```

An optional `--source-text /path/to/diss.txt` also checks the exact cached
extraction hash and heading positions. The checker performs no downloads.
It detects missing comparisons, changed source locations, and changed reviewed
modules, Lean sources, or dependency-lock snapshots. It does not check the truth
of a review's prose or rerun Lean. The recorded successful `./scripts/check.sh` result belongs
to the identified source snapshot; run that command for fresh proof validation.

When source files change, review the affected comparisons and dependencies,
run the relevant Lean validation, and update the snapshot with that evidence.
Changing a hash alone is not a semantic review. The unresolved qualifications
and the limited scope of unnumbered comparisons must remain explicit.

## Candidate labels without a dissertation heading

| Candidate label | Extraction line | Classification |
| --- | ---: | --- |
| Corollary 3.2 | 373 | A citation of reference [22]. The dissertation's own result 3.2 is a lemma. |
| Lemma 2.2 | 4582 | A citation of reference [59], in Section 10. |
| Lemma 14.2 | 5007 | A citation of reference [23], in Section 12. The dissertation's own result 14.2 is a remark. |
| Lemma 10.6 | 7228 | A running reference in the proof of Lemma 19.1. The cited estimate is headed Corollary 10.6 at line 4392. |

The index classifies all 22 nonheading occurrences among the generated
candidates, including repeated references to actual dissertation results.
The generated inventory remains unchanged so that it can still be checked
against the original extraction.

## Numbered remarks outside the generated inventory

| Remark | Extraction line | Focused audit |
| --- | ---: | --- |
| 10.9 | 4540 | [Section 10](SECTION_10.md) |
| 14.2 | 5968 | [Section 14](SECTION_14.md) |
| 18.4 | 6814 | [Section 18](SECTION_18.md) |
| 22.3 | 8373 | [Section 22](SECTION_22.md) |
| 23.3 | 8506 | [Section 23](SECTION_23.md) |
| A.6 | 10076 | [Appendix A](APPENDIX_A.md) |
| D.2 | 10344 | [Appendix D](APPENDIX_D.md) |
| D.3 | 10360 | [Appendix D](APPENDIX_D.md) |
| D.7 | 10605 | [Appendix D](APPENDIX_D.md) |

The occurrence of Remark 2.3 at line 10074 is a citation of reference [41],
Section IV, in the proof of Lemma A.5. It is excluded from this heading list.

Source lines count newline characters in the cached `pdftotext` extraction,
retaining form-feed characters. Source text and PDF hashes, the source URL,
and the one-based form-feed page convention are recorded in the JSON index.
These positions should not be recomputed using a line splitter that treats
form feeds as additional line breaks.
