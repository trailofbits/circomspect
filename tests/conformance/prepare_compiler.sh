#!/usr/bin/env bash
set -euo pipefail

readonly CIRCOM_TAG="v2.2.3"
readonly CIRCOM_COMMIT="ad44e915a12bb047b05745c2884aad9cc8326bc6"
readonly BUILD_ROOT="${1:?usage: prepare_compiler.sh BUILD_DIRECTORY}"
readonly SOURCE_DIR="${BUILD_ROOT}/circom-${CIRCOM_TAG}"

mkdir -p "${BUILD_ROOT}"
if [[ ! -d "${SOURCE_DIR}/.git" ]]; then
	GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null \
		git clone --depth 1 --branch "${CIRCOM_TAG}" \
		https://github.com/iden3/circom.git "${SOURCE_DIR}"
fi

actual_commit="$(git -C "${SOURCE_DIR}" rev-parse HEAD)"
if [[ "${actual_commit}" != "${CIRCOM_COMMIT}" ]]; then
	echo "Circom source revision mismatch: expected ${CIRCOM_COMMIT}, got ${actual_commit}" >&2
	exit 1
fi

cargo +1.98.1 build --release --locked -p circom --manifest-path "${SOURCE_DIR}/Cargo.toml"
"${SOURCE_DIR}/target/release/circom" --version
