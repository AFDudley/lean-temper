# lean-temper commit-boundary gate image, modeled on lean-mend's (exophial D49:
# exophial/docs/decisions/2026-10-14-gate-runs-in-a-container-built-from-the-judged-commit.md).
#
# exophial builds this file from a tar of the judged commit's tree (no .git, no .scratch),
# then runs `.exophial/config.yaml` gate.command (`.exophial/gate/gate.sh`) as the one
# process, with no bind mount. So every tool the gate calls is image content:
#   elan and the toolchain in lean-temper's lean-toolchain -> lake build
#   git, bash                                              -> .exophial/gate/gate.sh
# The layers before COPY do not depend on the judged tree, so they are reused between runs.
FROM debian:bookworm-slim

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates curl git bash zstd \
    && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/root/.elan HOME=/root
ENV PATH="/root/.elan/bin:${PATH}"
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --no-modify-path --default-toolchain none \
    && elan toolchain install leanprover/lean4:v4.35.0

WORKDIR /gate
COPY . .

# No ENTRYPOINT: exophial passes gate.command, which runs in WORKDIR /gate with this PATH.
