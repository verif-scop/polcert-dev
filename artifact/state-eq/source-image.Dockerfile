ARG POLCERT_DEPENDENCY_IMAGE=polcert-artifact:state-eq-2026-05-25-v2
FROM ${POLCERT_DEPENDENCY_IMAGE} AS development

ARG PLUTO_IMAGE
ARG PLUTO_GIT_REMOTE=https://github.com/verif-scop/pluto.git
ARG PLUTO_GIT_COMMIT
ARG POLCERT_GIT_COMMIT

USER root

# Keep the reviewed apt/opam closure, but update the separately pinned Pluto
# source and rebuild it for the v9 compiler image.
RUN git -C /pluto fetch "${PLUTO_GIT_REMOTE}" "${PLUTO_GIT_COMMIT}" \
  && git -C /pluto checkout "${PLUTO_GIT_COMMIT}" \
  && cd /pluto \
  && ./configure --enable-glpk --with-glpk-prefix=/usr \
  && make clean \
  && make -j"$(nproc)" \
  && make install

RUN find /polcert -mindepth 1 -maxdepth 1 -exec rm -rf {} + \
  && rm -rf /opt/polcert-artifact /artifact-results
COPY . /polcert/

WORKDIR /polcert
RUN eval "$(opam env)" && ./configure x86_64-linux

LABEL com.polcert.pluto.image="${PLUTO_IMAGE}" \
      com.polcert.pluto.remote="${PLUTO_GIT_REMOTE}" \
      com.polcert.pluto.commit="${PLUTO_GIT_COMMIT}"

ENV PLUTO_GIT_COMMIT="${PLUTO_GIT_COMMIT}" \
    POLCERT_PLUTO_IMAGE="${PLUTO_IMAGE}" \
    POLCERT_PLUTO_GIT_REMOTE="${PLUTO_GIT_REMOTE}" \
    POLCERT_PLUTO_GIT_COMMIT="${PLUTO_GIT_COMMIT}" \
    POLCERT_GIT_COMMIT="${POLCERT_GIT_COMMIT}"

ENTRYPOINT ["/bin/bash"]
