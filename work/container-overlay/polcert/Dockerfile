# Keep these defaults aligned with tools/ci/pluto-baseline.env.
ARG PLUTO_IMAGE=hughshine/pluto-verif:latest
ARG PLUTO_GIT_REMOTE=https://github.com/verif-scop/pluto.git
ARG PLUTO_GIT_COMMIT=7cb0892d42dd65fb083601750cad1a325688a366

FROM ${PLUTO_IMAGE}

ARG PLUTO_IMAGE
ARG PLUTO_GIT_REMOTE
ARG PLUTO_GIT_COMMIT

LABEL com.polcert.version="0.9" \
      com.polcert.pluto.image="${PLUTO_IMAGE}" \
      com.polcert.pluto.remote="${PLUTO_GIT_REMOTE}" \
      com.polcert.pluto.commit="${PLUTO_GIT_COMMIT}"

ENV POLCERT_PLUTO_IMAGE="${PLUTO_IMAGE}" \
    POLCERT_PLUTO_GIT_REMOTE="${PLUTO_GIT_REMOTE}" \
    POLCERT_PLUTO_GIT_COMMIT="${PLUTO_GIT_COMMIT}"

ENV TZ=Europe/Minsk
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

RUN  apt-get update \
  && apt-get install -y wget make m4 build-essential patch unzip git libgmp3-dev libgmp-dev libglpk-dev libeigen3-dev \
  && rm -rf /var/lib/apt/lists/*

RUN wget https://github.com/ocaml/opam/releases/download/2.0.8/opam-2.0.8-x86_64-linux --no-check-certificate -O opam && \
    chmod 744 opam && \
    mv opam /usr/local/bin/opam

RUN opam init -y --verbose --disable-sandboxing 

RUN test -r /root/.opam/opam-init/init.sh && . /root/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true

RUN opam switch create polcert 4.13.1

RUN opam pin -y add coq 8.13.2

RUN opam update && opam install -y zarith glpk menhir stdlib-shims

RUN echo 'eval $(opam env)' >> ~/.bashrc

# prepare the server for documentation
RUN apt-get update && apt-get install -y apache2 && apt-get clean && rm -rf /var/lib/apt/lists/*
ENV APACHE_RUN_USER  www-data
ENV APACHE_RUN_GROUP www-data
ENV APACHE_LOG_DIR   /var/log/apache2
ENV APACHE_PID_FILE  /var/run/apache2/apache2.pid
ENV APACHE_RUN_DIR   /var/run/apache2
ENV APACHE_LOCK_DIR  /var/lock/apache2
ENV APACHE_LOG_DIR   /var/log/apache2
RUN mkdir -p $APACHE_RUN_DIR
RUN mkdir -p $APACHE_LOCK_DIR
RUN mkdir -p $APACHE_LOG_DIR
COPY doc/index.html /var/www/html

EXPOSE 80

# prepare the editor, here we use vim
RUN apt-get update && apt-get install -y vim cloc && apt-get clean && rm -rf /var/lib/apt/lists/*

SHELL ["/bin/bash", "-c"]

COPY . /polcert/

WORKDIR /polcert/

RUN eval $(opam env) && ./configure x86_64-linux 
# RUN make && make test

ENTRYPOINT /usr/sbin/apache2 && bash
