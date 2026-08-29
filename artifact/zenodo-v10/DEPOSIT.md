# Zenodo Deposit Checklist

This file is for the artifact maintainer. It is not copied into the reviewer
package.

## Create the Upload Directory

Run from the control repository:

```sh
python3 artifact/zenodo-v10/bin/prepare_zenodo.py
```

The default input is the frozen v10 `final/` release directory. The default
output is the adjacent `zenodo-upload/` directory. The command verifies the
source and image hashes, release identity, successful CI metadata, and all
30 artifact results before writing any upload file.

The Docker tar is hard-linked when the input and output use the same file
system, with a byte-for-byte copy as the fallback. This saves 2.43 GB of local
disk space and does not change the file presented to Zenodo. Use
`--copy-docker` when the output must have an independent inode.

## Deposit Metadata

Use these values in the Zenodo draft:

| Field | Value |
| --- | --- |
| Resource type | Software |
| Title | PolCert: End-to-End Verified Polyhedral Compilation |
| Version | v10 |
| Publication date | 2026-08-29 |
| License | LGPL-2.1-or-later |
| Related identifier | GitHub tag `state-eq-polyhedral-verification-complete-2026-08-29-v10` |
| Keywords | verified compilation; polyhedral compilation; loop transformation; Rocq; translation validation |

Fill creators, affiliations, and ORCIDs from the final author list. Do not copy
the anonymous paper metadata into the public record.

Use a manual Zenodo draft when the paper needs a DOI before the GitHub release.
Reserve the DOI, add the version-specific DOI to the paper and artifact record,
then publish the record only after the author and license metadata are final.
The paper should cite the version DOI for this exact artifact, rather than only
the concept DOI shared by later versions.

## Upload Gate

Upload only the eight files in `zenodo-upload/`. Do not upload:

- the expanded `final/` tree, which contains more than 2,400 files;
- the parent release staging directory, which contains obsolete archives;
- `artifact/state-eq/`, which is the frozen v9 reference;
- paper workflow logs, internal review notes, or agent state.

Before publication:

```sh
cd output/releases/state-eq-polyhedral-verification-complete-2026-08-29-v10/zenodo-upload
sha256sum -c SHA256SUMS
./verify.sh evidence
```

Run `./verify.sh quick` on a second machine when possible. Confirm that Zenodo
shows eight top-level files and can browse `polcert-v10-evidence.zip`.
