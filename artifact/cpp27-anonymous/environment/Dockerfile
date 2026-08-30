ARG UBUNTU_IMAGE=ubuntu:20.04@sha256:8feb4d8ca5354def3d8fce243717141ce31e2c428701f6682bd2fafe15388214

FROM ${UBUNTU_IMAGE} AS pluto-base

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
       autoconf automake bison build-essential ca-certificates flex git \
       libclang-10-dev libeigen3-dev libglpk-dev libgmp-dev \
       libtool-bin llvm-10-dev m4 patch pkg-config python3 texinfo unzip wget \
    && rm -rf /var/lib/apt/lists/*

RUN update-alternatives --install /usr/bin/FileCheck FileCheck /usr/bin/FileCheck-10 100 \
    && update-alternatives --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-10 100

ARG PLUTO_BUILD_JOBS=4

FROM pluto-base AS rocq-toolchain

RUN wget -q \
      https://github.com/ocaml/opam/releases/download/2.0.8/opam-2.0.8-x86_64-linux \
      -O /usr/local/bin/opam \
    && echo "95365a873d9e3ae6fb48e6109b5fc5df3b4e526c9d65d20652a78e263f745a35  /usr/local/bin/opam" \
       | sha256sum -c - \
    && chmod 755 /usr/local/bin/opam

RUN opam init -y --disable-sandboxing --bare \
    && opam switch create polcert 4.13.1 \
    && opam install -y --switch=polcert \
       coq.8.13.2 dune.3.22.2 glpk.0.1.8 menhir.20260209 \
       ocamlfind.1.9.8 stdlib-shims.0.3.0 zarith.1.14

FROM pluto-base AS pluto-fixed-builder

ARG PLUTO_BUILD_JOBS
COPY third_party/pluto/fixed /pluto
WORKDIR /pluto
RUN git init -q \
    && git config user.name "Anonymous Artifact" \
    && git config user.email "artifact@invalid" \
    && git add -f . \
    && GIT_AUTHOR_DATE=2026-08-29T00:00:00Z \
       GIT_COMMITTER_DATE=2026-08-29T00:00:00Z \
       git commit -q -m "Fixed Pluto source snapshot" \
    && ./autogen.sh \
    && ./configure --enable-glpk --with-glpk-prefix=/usr \
    && jobs="$(nproc)" \
    && if [ "${jobs}" -gt "${PLUTO_BUILD_JOBS}" ]; then jobs="${PLUTO_BUILD_JOBS}"; fi \
    && make -j"${jobs}" \
    && make install

FROM pluto-base AS pluto-historical-builder

ARG PLUTO_BUILD_JOBS
COPY third_party/pluto/historical /opt/polcert/pluto-historical
WORKDIR /opt/polcert/pluto-historical
RUN git init -q \
    && git config user.name "Anonymous Artifact" \
    && git config user.email "artifact@invalid" \
    && git add -f . \
    && GIT_AUTHOR_DATE=2026-08-29T00:00:00Z \
       GIT_COMMITTER_DATE=2026-08-29T00:00:00Z \
       git commit -q -m "Historical Pluto source snapshot" \
    && ./autogen.sh \
    && ./configure --enable-glpk --with-glpk-prefix=/usr \
    && jobs="$(nproc)" \
    && if [ "${jobs}" -gt "${PLUTO_BUILD_JOBS}" ]; then jobs="${PLUTO_BUILD_JOBS}"; fi \
    && make -j"${jobs}"

FROM rocq-toolchain AS polcert-artifact

COPY --from=pluto-fixed-builder /pluto /pluto
COPY --from=pluto-fixed-builder /usr/local/ /usr/local/
COPY --from=pluto-historical-builder \
     /opt/polcert/pluto-historical /opt/polcert/pluto-historical
RUN ldconfig
COPY source /polcert
COPY environment/run-tests.sh /usr/local/bin/run-polcert-artifact

ENV POLCERT_PLUTO=/pluto/tool/pluto \
    POLCERT_REAL_PLUTO=/pluto/tool/pluto \
    POLCERT_POLYCC=/pluto/polycc \
    PLUTO_TEST_DIR=/pluto/test \
    POLCERT_BUGGY_ROOT=/opt/polcert/pluto-historical \
    POLCERT_BUGGY_PLUTO=/opt/polcert/pluto-historical/tool/pluto \
    POLCERT_BUGGY_POLYCC=/opt/polcert/pluto-historical/polycc

SHELL ["/bin/bash", "-c"]
WORKDIR /polcert
ARG PROOF_JOBS=auto
ARG BUILD_JOBS=auto
RUN fixed_revision="$(git -C /pluto rev-parse HEAD)" \
    && historical_revision="$(git -C /opt/polcert/pluto-historical rev-parse HEAD)" \
    && mkdir -p tools/ci \
    && printf 'PLUTO_GIT_COMMIT=%s\nPLUTO_BUGGY_GIT_COMMIT=%s\n' \
       "${fixed_revision}" "${historical_revision}" > tools/ci/pluto-baseline.env \
    && eval "$(opam env --switch=polcert)" \
    && ./configure x86_64-linux \
    && . tools/ci/ci_resources.sh \
    && proof_jobs="$(ci_choose_jobs PROOF_JOBS 2 6144)" \
    && build_jobs="$(ci_choose_jobs BUILD_JOBS 4 1536)" \
    && printf '[build-resources] proof_jobs=%s build_jobs=%s\n' \
       "${proof_jobs}" "${build_jobs}" \
    && make depend \
    && make -j"${proof_jobs}" proof \
    && make -s check-admitted \
    && make -j"${proof_jobs}" extraction \
    && make polcert.ini \
    && make .depend.extr \
    && make -f Makefile.extr -j"${build_jobs}" polcert \
    && make -f Makefile.extr -j"${build_jobs}" polopt

ENV PYTHONUNBUFFERED=1

ENTRYPOINT ["/usr/local/bin/run-polcert-artifact"]
CMD ["smoke"]
