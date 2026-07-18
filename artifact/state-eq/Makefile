POLCERT_SOURCE ?=
POLCERT_ARTIFACT_IMAGE ?= polcert-artifact:state-eq-2026-05-25-v2
POLCERT_ARTIFACT_OUTPUT ?= $(CURDIR)/results

.PHONY: validate build smoke review extended reproduce clean-results

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

clean-results:
	rm -rf "$(POLCERT_ARTIFACT_OUTPUT)"
