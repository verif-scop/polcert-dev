POLCERT_SOURCE ?=
POLCERT_ARTIFACT_IMAGE ?= polcert-artifact:state-eq-2026-05-25-v2
POLCERT_ARTIFACT_OUTPUT ?= $(CURDIR)/results
POLCERT_PUBLICATION_REF ?=
POLCERT_REVIEW_EVIDENCE ?= $(CURDIR)/evidence/2026-07-18-full-review.json
POLCERT_PUBLICATION_RECORD ?= $(CURDIR)/publication/publication-record.json

.PHONY: validate build smoke review extended reproduce publication-test publication-validate publish-reviewed-image clean-results

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

publication-test:
	python3 -m unittest tests/test_publish_reviewed_image.py

publication-validate:
	./bin/publish_reviewed_image.py \
		--registry-ref "$(POLCERT_PUBLICATION_REF)" \
		--review-evidence "$(POLCERT_REVIEW_EVIDENCE)" \
		--record "$(POLCERT_PUBLICATION_RECORD)" \
		--dry-run

publish-reviewed-image:
	./bin/publish_reviewed_image.py \
		--registry-ref "$(POLCERT_PUBLICATION_REF)" \
		--review-evidence "$(POLCERT_REVIEW_EVIDENCE)" \
		--record "$(POLCERT_PUBLICATION_RECORD)"

clean-results:
	rm -rf "$(POLCERT_ARTIFACT_OUTPUT)"
