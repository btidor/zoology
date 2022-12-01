import os
import subprocess

from Crypto.Hash import keccak


def compile_solidity(source: str, version: str) -> bytes:
    env = os.environ.copy()
    env["SOLC_VERSION"] = version
    output = subprocess.check_output(
        ["solc", "--bin-runtime", "-"], env=env, input=source.encode()
    )
    hexstr = output.splitlines()[-2].decode()
    return bytes.fromhex(hexstr)


def abiencode(signature: str) -> bytes:
    return keccak.new(data=signature.encode(), digest_bits=256).digest()[:4]
