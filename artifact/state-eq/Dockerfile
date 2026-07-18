ARG POLCERT_SOURCE_IMAGE=polcert-artifact-source:13295e741ad6
FROM ${POLCERT_SOURCE_IMAGE}

ARG POLCERT_ARTIFACT_ID
ARG POLCERT_SOURCE_TAG
ARG POLCERT_SOURCE_COMMIT
ARG POLCERT_SOURCE_TREE
ARG PLUTO_SOURCE_COMMIT

LABEL org.opencontainers.image.title="PolCert State.eq artifact" \
      org.opencontainers.image.description="Claim-oriented reproduction image for the completed State.eq-preserving PolCert milestone" \
      org.opencontainers.image.source="https://github.com/Hughshine/PolCert" \
      org.opencontainers.image.version="${POLCERT_SOURCE_TAG}" \
      org.opencontainers.image.revision="${POLCERT_SOURCE_COMMIT}" \
      io.polcert.artifact.id="${POLCERT_ARTIFACT_ID}" \
      io.polcert.source.tree="${POLCERT_SOURCE_TREE}" \
      io.polcert.pluto.revision="${PLUTO_SOURCE_COMMIT}" \
      io.polcert.review.network="none"

ENV POLCERT_ARTIFACT_ID="${POLCERT_ARTIFACT_ID}" \
    POLCERT_SOURCE_TAG="${POLCERT_SOURCE_TAG}" \
    POLCERT_SOURCE_COMMIT="${POLCERT_SOURCE_COMMIT}" \
    POLCERT_SOURCE_TREE="${POLCERT_SOURCE_TREE}" \
    POLCERT_ARTIFACT_OUTPUT="/artifact-results"

COPY manifest.json claims.json dependency-lock-audit.json /opt/polcert-artifact/
COPY in-image/review.sh in-image/run_claim_suite.py /opt/polcert-artifact/
RUN chmod 0755 /opt/polcert-artifact/review.sh /opt/polcert-artifact/run_claim_suite.py

WORKDIR /polcert
ENTRYPOINT ["/opt/polcert-artifact/review.sh"]
CMD ["full"]
