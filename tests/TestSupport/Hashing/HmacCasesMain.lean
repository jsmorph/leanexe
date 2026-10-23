import TestSupport.Hashing.HmacCases

/-! The cases of the modules `hmac_sha256` and `hmac_sha512` alone, for
`tests/verified/run.sh --cases hmac_sha256` or `--cases hmac_sha512`. -/

def main : IO Unit := TestSupport.Hashing.HmacCases.cases
