#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS_DIR="${STEVIA_TOOLS_DIR:-${ROOT_DIR}/.tools}"
BIN_DIR="${TOOLS_DIR}/bin"

VERIBLE_VERSION="${VERIBLE_VERSION:-v0.0-4053-g89d4d98a}"
SLANG_VERSION="${SLANG_VERSION:-v11.0}"
SBY_REF="${SBY_REF:-f57802a16613f013e84e024df50fc3f0ea74f88b}"
PYTHON_BIN="${PYTHON_BIN:-python3}"

mkdir -p "${TOOLS_DIR}" "${BIN_DIR}"

machine="$(uname -m)"
case "${machine}" in
  x86_64 | amd64)
    verible_arch="x86_64"
    slang_arch="x86_64"
    ;;
  aarch64 | arm64)
    verible_arch="arm64"
    echo "The pinned slang release currently provides Linux x86_64 binaries only." >&2
    echo "Use an x86_64 runner or install slang separately and put it on PATH." >&2
    exit 1
    ;;
  *)
    echo "Unsupported machine architecture: ${machine}" >&2
    exit 1
    ;;
esac

download_and_extract() {
  local url="$1"
  local archive="$2"
  local target_dir="$3"

  curl --fail --location --retry 3 --output "${archive}" "${url}"
  rm -rf "${target_dir}"
  mkdir -p "${target_dir}"
  tar -xzf "${archive}" -C "${target_dir}" --strip-components=1
}

install_verible() {
  local name="verible-${VERIBLE_VERSION}-linux-static-${verible_arch}"
  local install_dir="${TOOLS_DIR}/${name}"
  local archive="${TOOLS_DIR}/${name}.tar.gz"
  local url="https://github.com/chipsalliance/verible/releases/download/${VERIBLE_VERSION}/${name}.tar.gz"

  if [[ ! -x "${install_dir}/bin/verible-verilog-lint" ]]; then
    echo "Installing Verible ${VERIBLE_VERSION}"
    download_and_extract "${url}" "${archive}" "${install_dir}"
  fi

  ln -sfn "${install_dir}/bin/verible-verilog-lint" "${BIN_DIR}/verible-verilog-lint"
  ln -sfn "${install_dir}/bin/verible-verilog-format" "${BIN_DIR}/verible-verilog-format"
}

install_slang() {
  local install_dir="${TOOLS_DIR}/slang-${SLANG_VERSION}-linux-${slang_arch}"
  local archive="${TOOLS_DIR}/slang-${SLANG_VERSION}-linux-${slang_arch}.tar.gz"
  local url="https://github.com/MikePopoloski/slang/releases/download/${SLANG_VERSION}/slang-linux-${slang_arch}.tar.gz"

  if [[ ! -x "${install_dir}/slang" ]]; then
    echo "Installing slang ${SLANG_VERSION}"
    curl --fail --location --retry 3 --output "${archive}" "${url}"
    rm -rf "${install_dir}"
    mkdir -p "${install_dir}"
    tar -xzf "${archive}" -C "${install_dir}"
  fi

  ln -sfn "${install_dir}/slang" "${BIN_DIR}/slang"
}

install_sby() {
  local src_dir="${TOOLS_DIR}/sby-src"
  local install_dir="${TOOLS_DIR}/sby-install"

  if [[ ! -x "${install_dir}/bin/sby" ]]; then
    echo "Installing SymbiYosys ${SBY_REF}"
    rm -rf "${src_dir}" "${install_dir}"
    git init "${src_dir}"
    git -C "${src_dir}" remote add origin https://github.com/YosysHQ/sby.git
    git -C "${src_dir}" fetch --depth 1 origin "${SBY_REF}"
    git -C "${src_dir}" checkout --detach FETCH_HEAD
    make -C "${src_dir}" PREFIX="${install_dir}" install
  fi

  rm -f "${BIN_DIR}/sby"
  {
    echo "#!/usr/bin/env bash"
    echo "exec \"${install_dir}/bin/sby\" \"\$@\""
  } > "${BIN_DIR}/sby"
  chmod +x "${BIN_DIR}/sby"
}

install_python_deps() {
  if [[ ! -x "${ROOT_DIR}/.venv/bin/python" ]]; then
    "${PYTHON_BIN}" -m venv "${ROOT_DIR}/.venv"
  fi

  "${ROOT_DIR}/.venv/bin/python" -m pip install --upgrade pip

  if "${ROOT_DIR}/.venv/bin/python" -c 'import sys; raise SystemExit(sys.version_info <= (3, 13))'; then
    COCOTB_IGNORE_PYTHON_REQUIRES=1 "${ROOT_DIR}/.venv/bin/python" -m pip install -r "${ROOT_DIR}/requirements-dev.txt"
  else
    "${ROOT_DIR}/.venv/bin/python" -m pip install -r "${ROOT_DIR}/requirements-dev.txt"
  fi
}

install_verible
install_slang
install_sby
install_python_deps

echo "Installed tool wrappers:"
"${BIN_DIR}/slang" --version
"${BIN_DIR}/verible-verilog-lint" --version
"${BIN_DIR}/sby" --version
