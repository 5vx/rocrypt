# RoCrypt

## Description
A pure-Lua (5.1) cryptography module supporting:
- Cryptographic hash functions (CHF)
  - MD2, MD4, MD5
  - RIPEMD-128, RIPEMD-160
  - SHA1, SHA-224, SHA-256, SHA-384, SHA-512
  - SHA3-224, SHA3-256, SHA3-384, SHA3-512
  - SHAKE128, SHAKE256
- Cyclic redundancy checks (CRC) algorithms
  - CRC32
- Binary-to-hex encoding algorithms
  - Base64, Base91
- Asymmetric algorithms
  - RSA
- Symmetric algorithms
  - AES
- Shared-secret algorithms
  - HMAC
- UID (unique identifier) algorithms
  - Snowflake

## Credit
- RobloxGamerPro200007 - RSA function
- Egor-Skriptunoff - Creating the original SHA-2 & Keccak (SHA-3) backbones

## Usage

```lua
local RoCrypt = require(script.RoCrypt)
local hash = RoCrypt.sha256("Hello, World!")
```

```lua
local RoCrypt = require(script.RoCrypt)
local RSA = RoCrypt.rsa()
n, e, d = RSA.newKeys()
encrypted = RSA.crypt(n, 242351, e)
decrypted = RSA.crypt(n, encrypted, d)
print(decrypted[1]) -- Expected output: 242351
```