POLCERT_SOURCE ?=
POLCERT_ARTIFACT_IMAGE ?= polcert-artifact:state-eq-2026-08-26-v9-candidate
POLCERT_ARTIFACT_OUTPUT ?= $(CURDIR)/results
POLCERT_PUBLICATION_REF ?=
POLCERT_REVIEW_EVIDENCE ?= $(CURDIR)/evidence/2026-08-26-v9-full-review.json
POLCERT_PUBLICATION_RECORD ?= $(CURDIR)/publication/publication-record.json
POLCERT_DEPENDENCY_LOCK_DIR ?= $(CURDIR)/locks
POLCERT_DEPENDENCY_LOCK_ORIGIN_IMAGE ?= polcert-artifact:state-eq-2026-05-25-v2
POLCERT_DEPENDENCY_LOCK_ORIGIN_EVIDENCE ?= $(CURDIR)/evidence/2026-07-18-full-review.json
POLCERT_REVIEW_RESULTS ?= $(POLCERT_ARTIFACT_OUTPUT)
POLCERT_BUILD_METADATA ?= $(CURDIR)/build/build-metadata.json
POLCERT_REVIEW_EVIDENCE_OUTPUT ?= $(CURDIR)/evidence/2026-08-26-v9-full-review.json

.PHONY: validate build smoke review extended reproduce archive-full-review review-evidence-validate review-evidence-test claim-evidence-test dependency-lock-capture dependency-lock-verify dependency-lock-test publication-test publication-validate publish-reviewed-image clean-results

validate:
	./bin/build-image.sh --source "$(POLCERT_SOURCE)" --image "$(POLCERT_ARTIFACT_IMAGE)" --validate-only

build:
	./bin/build-image.sh --source "$(POLCERT_SOURCE)" --image "$(POLCERT_ARTIFACT_IMAGE)"

smoke:
	./bin/run-image.sh --image "$(POLCERT_ARTIFACT_IMAGE)" --output-dir "$(POLCERT_ARTIFACT_OUTPUT)" --mode smoke

review:
	./bin/run-image.sh --image "$(POLCERT_ARTIFACT_IMAGE)" --output-dir "$(POLCERT_ARTIFACT_OUTPUT)" --mode full

extended:
	./bin/run-image.sh --image "$(POLCERT_ARTIFACT_IMAGE)" --output-dir "$(POLCERT_ARTIFACT_OUTPUT)" --mode extended

reproduce: build
	$(MAKE) review

archive-full-review:
	./bin/archive_full_review.py create \
		--results-dir "$(POLCERT_REVIEW_RESULTS)" \
		--image "$(POLCERT_ARTIFACT_IMAGE)" \
		--build-metadata "$(POLCERT_BUILD_METADATA)" \
		--evidence "$(POLCERT_REVIEW_EVIDENCE_OUTPUT)"

review-evidence-validate:
	./bin/archive_full_review.py validate \
		--results-dir "$(POLCERT_REVIEW_RESULTS)" \
		--image "$(POLCERT_ARTIFACT_IMAGE)" \
		--build-metadata "$(POLCERT_BUILD_METADATA)" \
		--evidence "$(POLCERT_REVIEW_EVIDENCE_OUTPUT)"

review-evidence-test:
	python3 -m unittest tests/test_claim_evidence.py tests/test_archive_full_review.py

claim-evidence-test:
	python3 -m unittest tests/test_claim_evidence.py

dependency-lock-capture:
	./bin/dependency_lock.py capture-image \
		--image "$(POLCERT_DEPENDENCY_LOCK_ORIGIN_IMAGE)" \
		--review-evidence "$(POLCERT_DEPENDENCY_LOCK_ORIGIN_EVIDENCE)" \
		--manifest "$(CURDIR)/manifest.json" \
		--output-dir "$(POLCERT_DEPENDENCY_LOCK_DIR)"

dependency-lock-verify:
	./bin/dependency_lock.py verify-image \
		--image "$(POLCERT_ARTIFACT_IMAGE)" \
		--lock "$(POLCERT_DEPENDENCY_LOCK_DIR)/dependency-lock.json" \
		--manifest "$(CURDIR)/manifest.json"

dependency-lock-test:
	python3 -m unittest tests/test_dependency_lock.py

publication-test:
	python3 -m unittest tests/test_publish_reviewed_image.py tests/test_candidate_boundary.py tests/test_claim_evidence.py tests/test_archive_full_review.py

publication-validate:
	./bin/publish_reviewed_image.py \
		--registry-ref "$(POLCERT_PUBLICATION_REF)" \
		--review-evidence "$(POLCERT_REVIEW_EVIDENCE)" \
		--review-results "$(POLCERT_REVIEW_RESULTS)" \
		--build-metadata "$(POLCERT_BUILD_METADATA)" \
		--record "$(POLCERT_PUBLICATION_RECORD)" \
		--dry-run

publish-reviewed-image:
	./bin/publish_reviewed_image.py \
		--registry-ref "$(POLCERT_PUBLICATION_REF)" \
		--review-evidence "$(POLCERT_REVIEW_EVIDENCE)" \
		--review-results "$(POLCERT_REVIEW_RESULTS)" \
		--build-metadata "$(POLCERT_BUILD_METADATA)" \
		--record "$(POLCERT_PUBLICATION_RECORD)"

clean-results:
	rm -rf "$(POLCERT_ARTIFACT_OUTPUT)"
