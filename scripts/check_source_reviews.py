#!/usr/bin/env python3
"""Check the published source-review snapshot, not mathematical completeness.

This verifies heading coverage, references, and hashes of the reviewed modules
and the Lean sources present at validation. It does not infer that a claim is
proved from a review status or declaration name. Run scripts/check.sh separately
for current Lean elaboration and the transitive axiom audit.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def repository_file(root, name):
    path = PurePosixPath(name)
    require(not path.is_absolute() and '..' not in path.parts,
            f'Invalid repository-relative path: {name}')
    target = (root / name).resolve()
    require(target.is_relative_to(root) and target.is_file(),
            f'Missing repository file: {name}')
    return target


def lean_source_snapshot(root):
    """Hash file names and contents; detect added, removed, or changed sources."""
    files = [*root.joinpath('NLS').rglob('*.lean'),
             *root.joinpath('scripts').rglob('*.lean'),
             root / 'NLS.lean', root / 'lakefile.toml',
             root / 'lean-toolchain', root / 'lake-manifest.json']
    rows = sorted((path.relative_to(root).as_posix(), sha256(path)) for path in files)
    digest = hashlib.sha256(json.dumps(rows, separators=(',', ':')).encode()).hexdigest()
    return {'files': len(rows), 'sha256': digest}


def reviewed_headings(index):
    rows = {}
    for candidate in index['candidate_labels']:
        if not candidate['has_statement_heading']:
            continue
        positions = [x['line'] for x in candidate['occurrences']
                     if x['classification'] == 'statement_heading']
        require(len(positions) == 1, f'Ambiguous heading: {candidate["label"]}')
        label = candidate['label']
        require(label not in rows, f'Duplicate heading: {label}')
        rows[label] = (positions[0], candidate['focused_audit'])
    for remark in index['additional_remark_headings']:
        label = remark['label']
        require(label not in rows, f'Duplicate heading: {label}')
        rows[label] = (remark['line'], remark['focused_audit'])
    return rows


def validate(root, manifest, source_text=None):
    require(manifest['schema_version'] == 1, 'Unsupported review-index schema')
    require(manifest['scope']['claims_complete_formalization'] is False,
            'An integrity checker cannot certify complete formalization')
    source = manifest['source']
    headings_path = repository_file(root, source['heading_index'])
    require(sha256(headings_path) == source['heading_index_sha256'],
            'The reviewed heading index changed; reconcile its source locations')
    headings = json.loads(headings_path.read_text(encoding='utf-8'))
    for key in ['source_text_sha256', 'source_pdf_sha256']:
        require(headings[key] == source[key], f'Inconsistent {key}')
    expected = reviewed_headings(headings)
    records = manifest['reviews']
    require(records, 'No source reviews were supplied')
    modules = {}
    hash_checks = 0
    for review_id, review in records.items():
        hashes = review['reviewed_module_hashes']
        require(hashes, f'Review has no module evidence: {review_id}')
        require(review.get('qualification'), f'Missing review qualification: {review_id}')
        for name, digest in hashes.items():
            require(name.startswith('NLS/') and name.endswith('.lean'),
                    f'Invalid reviewed module path: {name}')
            require(sha256(repository_file(root, name)) == digest,
                    f'Reviewed module changed: {name} ({review_id})')
            require(name not in modules or modules[name] == digest,
                    f'Conflicting module snapshots: {name}')
            modules[name] = digest
            hash_checks += 1
    observed = {}
    for row in manifest['named_statements']:
        label = row['label']
        require(label not in observed, f'Duplicate comparison: {label}')
        require(row['review'] in records, f'Unknown review for {label}')
        require(row.get('reviewed_claims'), f'Empty comparison: {label}')
        require(row.get('review_qualification'), f'Missing comparison qualification: {label}')
        repository_file(root, row['focused_audit'])
        observed[label] = (row['source_line'], row['focused_audit'])
    require(observed == expected,
            'Named comparisons differ from the reviewed headings or their source locations')
    counts = {'named_comparisons': len(observed), 'review_records': len(records),
              'module_hash_checks': hash_checks, 'distinct_modules': len(modules)}
    require(counts == manifest['counts'], 'Recorded review counts do not match the index')
    require(lean_source_snapshot(root) == manifest['validation_snapshot']['lean_sources'],
            'The Lean source or dependency-lock snapshot changed; update the review and validation evidence')
    if source_text is not None:
        require(sha256(source_text) == source['source_text_sha256'],
                'The supplied source extraction differs from the reviewed extraction')
        lines = source_text.read_text(encoding='utf-8').split('\n')
        for label, (line, _) in expected.items():
            require(1 <= line <= len(lines) and label in lines[line - 1],
                    f'Heading not present at the recorded newline position: {label}')
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--index', type=Path, help='Alternative review index for checking')
    parser.add_argument('--source-text', type=Path,
                        help='Optional local pdftotext extraction; no download is performed')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    index = args.index or root / 'coverage/source-review-index.json'
    try:
        counts = validate(root, json.loads(index.read_text(encoding='utf-8')), args.source_text)
    except (ValueError, KeyError, TypeError, OSError) as error:
        raise SystemExit(f'Source-review integrity check failed: {error}') from error
    print('Source-review integrity check passed: ' + json.dumps(counts))
    print('This checks recorded evidence, not mathematical completeness. '
          'Source qualifications remain; run ./scripts/check.sh for current Lean validation.')


if __name__ == '__main__':
    main()
